-- Analyzetime types
module Language.Edh.Meta.AtTypes where

import Control.Concurrent.STM
import Data.Vector (Vector)
import Language.Edh.EHI
import Language.Edh.Meta.AQ
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
    el'backlog :: !(TVar (FIFO AnalysisInQueue)),
    el'context :: !EL'Context,
    el'ets :: !EdhThreadState
  }

type AnalysisInQueue = STM () -> STM ()

el'PostAnalysis :: EL'AnalysisState -> AnalysisInQueue -> STM ()
el'PostAnalysis !eas !aiq = modifyTVar' (el'backlog eas) $ fifoEnque aiq

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

    -- | attribute definitions collected for current module
    el'ctx'attr'defs :: !(TVar [EL'AttrDef]),
    -- | attribute references collected for current module
    el'ctx'attr'refs :: !(TVar [EL'AttrRef]),
    -- | diagnostics collector in context
    el'ctx'diags :: !(TVar [EL'Diagnostic])
  }

data EL'ScopeWIP
  = EL'ProcFlow !EL'ProcWIP
  | EL'DefineClass !EL'ClassWIP !EL'ProcWIP
  | EL'InitObject !EL'Object !EL'ProcWIP
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

el'ContextModule :: EL'Context -> EL'ModuSlot
el'ContextModule !eac = case el'ContextModule' eac of
  Nothing -> error "missing context module"
  Just (!ms, _) -> ms

el'ContextModule' :: EL'Context -> Maybe (EL'ModuSlot, EL'ResolvingModu)
el'ContextModule' !eac = go $ el'ctx'scope eac : el'ctx'outers eac
  where
    go [] = Nothing
    go (scope : outers) = case scope of
      EL'InitModule !ms !mi _ -> Just (ms, mi)
      _ -> go outers

el'ContextObject :: EL'Context -> EL'Object
el'ContextObject = el'scope'this'obj . el'ProcWIP . el'ctx'scope

-- | a class defining procedure
data EL'ClassWIP = EL'ClassWIP
  { -- | the class object itself being defined
    el'class'obj'wip :: !EL'Object,
    -- | stub object instance for analysis of methods
    el'class'stub'wip :: !EL'Object
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
    -- | this object in context
    -- can be the toplevel module object, a class object being defined, a
    -- namespace object being initialized, or a stub object for methods
    -- being analyzed
    el'scope'this'obj :: !EL'Object,
    -- | accumulated inner scopes lately
    el'scope'inner'scopes'wip :: !(TVar [EL'Scope]),
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
    el'branch'regions'wip :: !(TVar [EL'Region])
  }

recordAttrDef :: EL'Context -> EL'AttrDef -> STM ()
recordAttrDef !eac !sym = modifyTVar' (el'ctx'attr'defs eac) (sym :)

recordAttrRef :: EL'Context -> EL'AttrRef -> STM ()
recordAttrRef !eac !sym = modifyTVar' (el'ctx'attr'refs eac) (sym :)

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
    Just !def -> case el'UltimateValue $ el'attr'def'value def of
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
el'ResolveAttrAddr !eas (AttrAddrSrc MissedAttrName !addr'span) = do
  el'LogDiag
    (el'ctx'diags $ el'context eas)
    el'Error
    addr'span
    "missing-attr"
    "missing attribute name"
  return Nothing
el'ResolveAttrAddr !eas (AttrAddrSrc MissedAttrSymbol !addr'span) = do
  el'LogDiag
    (el'ctx'diags $ el'context eas)
    el'Error
    addr'span
    "missing-sym"
    "missing symbolic attribute name"
  return Nothing

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
