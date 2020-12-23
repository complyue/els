-- Analyzetime types
module Language.Edh.Meta.AtTypes where

import Control.Concurrent.STM
import qualified Data.Map.Strict as TreeMap
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
  = EL'ProcFlow !EL'ProcWIP
  | EL'DefineClass !EL'ClassWIP !EL'ProcWIP
  | EL'InitObject !EL'ObjectWIP !EL'ProcWIP
  | EL'InitModule !EL'ModuSlot !EL'ResolvingModu !EL'ProcWIP

el'ProcWIP :: EL'ScopeWIP -> EL'ProcWIP
el'ProcWIP (EL'ProcFlow p) = p
el'ProcWIP (EL'DefineClass _ p) = p
el'ProcWIP (EL'InitObject _ p) = p
el'ProcWIP (EL'InitModule _ _ p) = p

el'BranchWIP :: EL'ScopeWIP -> EL'BranchWIP
el'BranchWIP = el'scope'branch'wip . el'ProcWIP

el'SwitchBranch :: EL'BranchWIP -> EL'ScopeWIP -> EL'ScopeWIP
el'SwitchBranch !bwip = \case
  EL'ProcFlow !p -> EL'ProcFlow p {el'scope'branch'wip = bwip}
  EL'DefineClass !c !p -> EL'DefineClass c p {el'scope'branch'wip = bwip}
  EL'InitObject !o !p -> EL'InitObject o p {el'scope'branch'wip = bwip}
  EL'InitModule !ms !resolving !p ->
    EL'InitModule ms resolving p {el'scope'branch'wip = bwip}

el'ContextModule :: EL'Context -> Maybe (EL'ModuSlot, EL'ResolvingModu)
el'ContextModule !eac = go $ el'ctx'scope eac : el'ctx'outers eac
  where
    go [] = Nothing
    go (scope : outers) = case scope of
      EL'InitModule !ms !mi _ -> Just (ms, mi)
      _ -> go outers

el'ContextInstance :: EL'Context -> EL'ArtsWIP
el'ContextInstance !eac = go $ el'ctx'scope eac : el'ctx'outers eac
  where
    go [] =
      -- error "bug: impossible"
      el'scope'attrs'wip $ el'ProcWIP $ el'ctx'scope eac
    go (scope : outers) = case scope of
      EL'InitModule _ _ !pwip -> el'scope'attrs'wip pwip
      EL'InitObject !owip _pwip -> el'obj'attrs'wip owip
      EL'DefineClass !cwip _pwip -> el'inst'attrs'wip cwip
      _ -> go outers

-- | an object initializing procedure, by far tends to be a namespace defining
-- procedure
data EL'ObjectWIP = EL'ObjectWIP
  { -- | all attributes assigned to @this.xxx@
    el'obj'attrs'wip :: !EL'ArtsWIP,
    -- | all @extends@ appeared in the direct scope and nested scopes (i.e.
    -- super objects),  up to time of analysis
    el'obj'exts'wip :: !(TVar [EL'Class]),
    -- | last appearances of exported artifacts in the direct scope and nested
    -- (method) scopes (i.e. object exports), up to time of analysis
    el'obj'exps'wip :: !EL'ArtsWIP
  }

-- | a class defining procedure
data EL'ClassWIP = EL'ClassWIP
  { -- | all attributes assigned to @this.xxx@ from methods (esp. @__init__()@)
    el'inst'attrs'wip :: !EL'ArtsWIP,
    -- | all `extends` appeared in the direct class scope (i.e. super classes),
    --  up to time of analysis
    el'class'exts'wip :: !(TVar [EL'Class]),
    -- | all `extends` appeared in nested (method) scopes (i.e. super objects),
    --  up to time of analysis
    el'inst'exts'wip :: !(TVar [EL'Class]),
    -- | last appearances of exported artifacts in the direct class scope (i.e.
    -- class exports), up to time of analysis
    el'class'exps'wip :: !EL'ArtsWIP,
    -- | last appearances of exported artifacts in nested (method) scopes (i.e.
    -- object exports), up to time of analysis
    el'inst'exps'wip :: !EL'ArtsWIP
  }

-- flow within a procedure, the procedure can be a vanilla method, a generator,
-- a producer, an operator, or an (vanilla/generator/producer) arrow procedure,
-- also maybe a bit confusing, it can be a scoped block.
--
-- when defining a class, initializing an object (usually either a namespace
-- object or a module object), there is a procedure undergoing as well.
data EL'ProcWIP = EL'ProcWIP
  { -- | current branch of control flow
    el'scope'branch'wip :: !EL'BranchWIP,
    -- | last appearances of attributes encountered, up to time of analysis
    el'scope'attrs'wip :: !EL'ArtsWIP,
    -- | this points to `el'modu'exts'wip` or `el'obj'exts'wip` or
    -- `el'class'exts'wip` or `el'inst'exts'wip` whichever is appropriate
    el'scope'exts'wip :: !(TVar [EL'Class]),
    -- | this points to `el'modu'exps'wip` or `el'obj'exps'wip` or
    -- `el'class'exps'wip` or `el'inst'exps'wip` whichever is appropriate
    el'scope'exps'wip :: !EL'ArtsWIP,
    -- | accumulated inner scopes lately
    el'scope'inner'scopes'wip :: !(TVar [EL'Scope]),
    -- | accumulated symbols lately
    el'scope'symbols'wip :: !(TVar (TreeMap.Map SrcPos EL'AttrSym)),
    -- | accumulated regions lately
    el'scope'regions'wip :: !(TVar [EL'Region])
  }

-- | the flow of an execution branch, with artifacts installed to the respective
-- scope incrementally
data EL'BranchWIP = EL'BranchWIP
  { -- | last appearances of attributes encountered, up to time of analysis
    el'branch'attrs'wip :: !EL'ArtsWIP,
    -- | last appearances of effectful artifacts, up to time of analysis
    el'branch'effs'wip :: !EL'ArtsWIP,
    -- | last appearances of annotations encountered in the direct class scope,
    -- up to time of analysis
    el'branch'annos'wip :: !(IOPD AttrKey EL'AttrAnno),
    -- | open regions lately
    el'branch'regions'wip :: !(TVar [EL'RegionWIP])
  }

data EL'RegionWIP = EL'RegionWIP
  { -- | start position of the region
    el'region'wip'start :: !SrcPos,
    -- | artifacts available in the region
    el'region'attrs'wip :: !EL'Artifacts
  }

recordScopeSymbol :: EL'ProcWIP -> EL'AttrSym -> STM ()
recordScopeSymbol !pwip !sym = case sym of
  EL'DefSym !def ->
    let !symKeyPos = src'end $ el'attr'def'focus def
     in modifyTVar' syms $ TreeMap.insert symKeyPos sym
  EL'RefSym !ref ->
    let AttrAddrSrc _ !ref'span = el'attr'ref'addr ref
        !symKeyPos = src'end ref'span
     in modifyTVar' syms $ TreeMap.insert symKeyPos sym
  where
    !syms = el'scope'symbols'wip pwip

el'ResolveLexicalAttr :: [EL'ScopeWIP] -> AttrKey -> STM (Maybe EL'AttrDef)
el'ResolveLexicalAttr [] _ = return Nothing
el'ResolveLexicalAttr (swip : outers) !key =
  iopdLookup key (el'branch'attrs'wip $ el'BranchWIP swip) >>= \case
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
  iopdLookup key $ el'branch'annos'wip $ el'BranchWIP swip

el'RunTx :: EL'AnalysisState -> EL'Tx -> STM ()
el'RunTx !eas !act = act eas
{-# INLINE el'RunTx #-}

el'ExitTx :: EL'TxExit a -> a -> EL'Tx
el'ExitTx !exit !a !eas = exit a eas
{-# INLINE el'ExitTx #-}

el'Exit :: EL'AnalysisState -> EL'TxExit a -> a -> STM ()
el'Exit !eas !exit !a = exit a eas
{-# INLINE el'Exit #-}
