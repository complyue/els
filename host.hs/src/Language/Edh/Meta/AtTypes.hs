-- Analyzetime types
module Language.Edh.Meta.AtTypes where

import Control.Concurrent.STM
import Data.HashMap.Strict (HashMap)
import Data.Vector (Vector)
import Language.Edh.EHI
import Language.Edh.Meta.Model
import Prelude

data EL'World = EL'World
  { -- this vector of home records should hold the invariant that sorted by
    -- their respective path, modifications should be mutually exclusive by
    -- taking from and putting back to this `TMVar`
    el'homes :: !(TMVar (Vector EL'Home)),
    -- | root artifacts at analysis time
    --
    -- this corresponds to root scope at runtime
    el'ambient :: !EL'Artifacts
  }

type EL'Analysis a = EL'TxExit a -> EL'Tx

type EL'TxExit a = a -> EL'Tx

type EL'Tx = EL'AnalysisState -> STM ()

data EL'AnalysisState = EL'AnalysisState
  { el'world :: !EL'World,
    el'context :: !EL'Context,
    el'ets :: !EdhThreadState
  }

-- | analysis context
data EL'Context = EL'Context
  { -- | current scope work-in-progress
    el'ctx'scope :: !EL'ScopeWIP,
    -- | lexical outer scopes work-in-progress
    el'ctx'outers :: ![EL'ScopeWIP],
    --

    -- | whether it's discouraged for procedure definitions or similar
    -- expressions from installing their results as attributes into the
    -- context scope
    el'ctx'pure :: !Bool,
    -- | whether running within an exporting stmt
    el'ctx'exporting :: !Bool,
    -- | whether running within an effect stmt
    el'ctx'eff'defining :: !Bool,
    --

    -- | diagnostics collector in context
    el'ctx'diags :: !(TVar [EL'Diagnostic])
  }

data EL'ScopeWIP
  = EL'ProcWIP !EL'AnaProc
  | EL'ClassWIP !EL'DefineClass !EL'AnaProc
  | EL'ObjectWIP !EL'InitObject !EL'AnaProc
  | EL'ModuWIP !EL'ModuSlot !EL'InitModu !EL'AnaProc

el'ProcWIP :: EL'ScopeWIP -> EL'AnaProc
el'ProcWIP (EL'ProcWIP p) = p
el'ProcWIP (EL'ClassWIP _ p) = p
el'ProcWIP (EL'ObjectWIP _ p) = p
el'ProcWIP (EL'ModuWIP _ _ p) = p

el'ContextModule :: EL'Context -> Maybe (EL'ModuSlot, EL'InitModu)
el'ContextModule !eac = go $ el'ctx'scope eac : el'ctx'outers eac
  where
    go [] = Nothing
    go (scope : outers) = case scope of
      EL'ModuWIP !ms !mi _ -> Just (ms, mi)
      _ -> go outers

-- | a modu initializing procedure
data EL'InitModu = EL'InitModu
  { -- | all `extends` appeared in the direct scope and nested scopes (i.e.
    -- super modules),  up to time of analysis
    el'modu'exts'wip :: !(TVar [EL'Object]),
    -- | 1st appearances of exported artifacts in the direct scope and nested
    -- (method) scopes (i.e. module exports), up to time of analysis
    el'modu'exps'wip :: !EL'ArtsWIP,
    -- | dependencies modules pending to be imported, there may be re-exports
    -- not yet appeared in `el'modu'exps'wip`, before this map returns empty
    --
    -- this will finally be the `el'pending'imps` field of the
    -- `EL'ResolvedModule` record
    el'modu'imps'wip :: !(TVar (HashMap EL'ModuSlot Bool)),
    -- | this will finally be the `el'resolved'dependencies` field of the
    -- `EL'ResolvedModule` record
    el'modu'dependencies :: !(TVar (HashMap EL'ModuSlot Bool))
  }

-- | an object initializing procedure, by far tends to be a namespace procedure
data EL'InitObject = EL'InitObject
  { -- | all `extends` appeared in the direct scope and nested scopes (i.e.
    -- super objects),  up to time of analysis
    el'obj'exts'wip :: !(TVar [EL'Object]),
    -- | 1st appearances of exported artifacts in the direct scope and nested
    -- (method) scopes (i.e. object exports), up to time of analysis
    el'obj'exps'wip :: !EL'ArtsWIP
  }

-- | a class defining procedure
data EL'DefineClass = EL'DefineClass
  { -- | all `extends` appeared in the direct class scope (i.e. super classes),
    --  up to time of analysis
    el'class'exts'wip :: !(TVar [EL'Object]),
    -- | all `extends` appeared in nested (method) scopes (i.e. super objects),
    --  up to time of analysis
    el'inst'exts'wip :: !(TVar [EL'Object]),
    -- | 1st appearances of exported artifacts in the direct class scope (i.e.
    -- class exports), up to time of analysis
    el'class'exps'wip :: !EL'ArtsWIP,
    -- | 1st appearances of exported artifacts in nested (method) scopes (i.e.
    -- object exports), up to time of analysis
    el'inst'exps'wip :: !EL'ArtsWIP
  }

-- a method procedure, including vanilla method, generator, producer, operator,
-- (vanilla/generator/producer) arrow, and maybe a bit confusing, scoped blocks
data EL'AnaProc = EL'AnaProc
  { -- | this points to `el'modu'exts'wip` or `el'obj'exts'wip` or
    -- `el'class'exts'wip` or `el'inst'exts'wip` whichever is appropriate
    el'scope'exts'wip :: !(TVar [EL'Object]),
    -- | this points to `el'modu'exps'wip` or `el'obj'exps'wip` or
    -- `el'class'exps'wip` or `el'inst'exps'wip` whichever is appropriate
    el'scope'exps'wip :: !EL'ArtsWIP,
    -- | last appearances of attributes encountered, up to time of analysis
    el'scope'attrs'wip :: !EL'ArtsWIP,
    -- | 1st appearances of effectful artifacts, up to time of analysis
    el'scope'effs'wip :: !EL'ArtsWIP,
    -- | last appearances of annotations encountered in the direct class scope,
    -- up to time of analysis
    el'scope'annos'wip :: !(IOPD AttrKey EL'AttrAnno),
    -- | accumulated inner scopes lately
    el'scope'inner'scopes'wip :: !(TVar [EL'Scope]),
    -- | accumulated regions lately
    el'scope'regions'wip :: !(TVar [EL'Region]),
    -- | accumulated symbols lately
    el'scope'symbols'wip :: !(TVar [EL'AttrSym])
  }

el'ResolveLexicalAttr :: [EL'ScopeWIP] -> AttrKey -> STM (Maybe EL'AttrDef)
el'ResolveLexicalAttr [] _ = return Nothing
el'ResolveLexicalAttr (swip : outers) !key =
  iopdLookup key (el'scope'attrs'wip $ el'ProcWIP swip) >>= \case
    Nothing -> el'ResolveLexicalAttr outers key
    Just !def -> return $ Just def

el'ResolveContextAttr :: EL'AnalysisState -> AttrKey -> STM (Maybe EL'AttrDef)
el'ResolveContextAttr !eas !key =
  el'ResolveLexicalAttr (el'ctx'scope eac : el'ctx'outers eac) key
    >>= \case
      Nothing -> return $ odLookup key $ el'ambient $ el'world eas
      result@Just {} -> return result
  where
    !eac = el'context eas

el'ResolveAttrAddr :: EL'AnalysisState -> AttrAddrSrc -> STM (Maybe AttrKey)
el'ResolveAttrAddr _ (AttrAddrSrc (NamedAttr !attrName) _) =
  return $ Just $ AttrByName attrName
el'ResolveAttrAddr _ (AttrAddrSrc (QuaintAttr !attrName) _) =
  return $ Just $ AttrByName attrName
el'ResolveAttrAddr !eas (AttrAddrSrc (SymbolicAttr !symName) !addr'span) =
  el'ResolveContextAttr eas (AttrByName symName) >>= \case
    Nothing -> do
      el'LogDiag
        diags
        el'Error
        addr'span
        "bad-attr-ref"
        "no such attribute defined"
      return Nothing
    Just !def -> case el'UltimateValue def of
      EL'Const (EdhSymbol !symKey) -> return $ Just $ AttrBySym symKey
      EL'Const (EdhString !nameKey) -> return $ Just $ AttrByName nameKey
      _ -> do
        el'LogDiag
          diags
          el'Warning
          addr'span
          "dyn-attr-ref"
          "dynamic attribute reference"
        !dynSym <- mkSymbol "<dynamic-attr-key>"
        return $ Just $ AttrBySym dynSym
  where
    eac = el'context eas
    diags = el'ctx'diags eac

el'ResolveAnnotation :: EL'ScopeWIP -> AttrKey -> STM (Maybe EL'AttrAnno)
el'ResolveAnnotation !swip !key =
  iopdLookup key $ el'scope'annos'wip $ el'ProcWIP swip

el'RunTx :: EL'AnalysisState -> EL'Tx -> STM ()
el'RunTx !eas !act = act eas
{-# INLINE el'RunTx #-}

el'ExitTx :: EL'TxExit a -> a -> EL'Tx
el'ExitTx !exit !a !eas = exit a eas
{-# INLINE el'ExitTx #-}

el'Exit :: EL'AnalysisState -> EL'TxExit a -> a -> STM ()
el'Exit !eas !exit !a = exit a eas
{-# INLINE el'Exit #-}
