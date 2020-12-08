module Language.Edh.Meta.RtTypes where

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
    -- | signal for end-of-world
    el'eow :: !EventSink
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
  = EL'ProcWIP !EL'RunProc
  | EL'ClassWIP !EL'DefineClass !EL'RunProc
  | EL'ObjectWIP !EL'InitObject !EL'RunProc
  | EL'ModuWIP !EL'ModuSlot !EL'InitModu !EL'RunProc

el'ProcWIP :: EL'ScopeWIP -> EL'RunProc
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
    -- | other modules those should be invalidated once this module is changed
    --
    -- note a dependant may stop depending on this module due to src changes,
    -- so cross checking of its `el'modu'dependencies` should be performed and
    -- have this `el'modu'dependants` updated upon such changes
    el'modu'dependants :: !(TVar (HashMap EL'ModuSlot Bool)),
    -- | other modules this module depends on
    --
    -- a dependency module's `el'modu'dependants` should be updated marking
    -- this module as a dependant as well
    --
    -- note after invalidated, re-analysation of this module may install a new
    -- version of this map reflecting dependencies up-to-date
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
data EL'RunProc = EL'RunProc
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

el'ResolveContextAttr :: EL'Context -> AttrKey -> STM (Maybe EL'AttrDef)
el'ResolveContextAttr !eac !key =
  el'ResolveLexicalAttr (el'ctx'scope eac : el'ctx'outers eac) key

el'ResolveAttrAddr :: EL'Context -> AttrAddrSrc -> STM (Maybe AttrKey)
el'ResolveAttrAddr _ (AttrAddrSrc (NamedAttr !attrName) _) =
  return $ Just $ AttrByName attrName
el'ResolveAttrAddr _ (AttrAddrSrc (QuaintAttr !attrName) _) =
  return $ Just $ AttrByName attrName
el'ResolveAttrAddr !eac (AttrAddrSrc (SymbolicAttr !symName) !addr'span) =
  el'ResolveContextAttr eac (AttrByName symName) >>= \case
    Nothing -> return Nothing
    Just !def -> case el'UltimateValue def of
      EL'Const (EdhSymbol !symVal) -> return $ Just $ AttrBySym symVal
      EL'Const (EdhString !nameVal) -> return $ Just $ AttrByName nameVal
      _ -> do
        el'LogDiag
          diags
          el'Error
          addr'span
          "bad-attr-ref"
          "no such attribute defined"
        return Nothing
  where
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
