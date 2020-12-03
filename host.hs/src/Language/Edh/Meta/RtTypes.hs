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

el'wip'proc :: EL'ScopeWIP -> EL'RunProc
el'wip'proc (EL'ProcWIP p) = p
el'wip'proc (EL'ClassWIP _ p) = p
el'wip'proc (EL'ObjectWIP _ p) = p
el'wip'proc (EL'ModuWIP _ _ p) = p

el'ContextModule :: EL'Context -> Maybe EL'ModuSlot
el'ContextModule !eac = go $ el'ctx'scope eac : el'ctx'outers eac
  where
    go [] = Nothing
    go (scope : outers) = case scope of
      EL'ModuWIP !ms _ _ -> Just ms
      _ -> go outers

-- | a modu initializing procedure
data EL'InitModu = EL'InitModu
  { -- | all `extends` appeared in the direct scope and nested scopes (i.e.
    -- super modules),  up to time of analysis
    el'modu'exts'wip :: !(TVar [EL'AttrRef]),
    -- | 1st appearances of exported artifacts in the direct scope and nested
    -- (method) scopes (i.e. module exports), up to time of analysis
    el'modu'exps'wip :: !EL'Exports,
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
    el'obj'exts'wip :: !(TVar [EL'AttrRef]),
    -- | 1st appearances of exported artifacts in the direct scope and nested
    -- (method) scopes (i.e. object exports), up to time of analysis
    el'obj'exps'wip :: !EL'Exports
  }

-- | a class defining procedure
data EL'DefineClass = EL'DefineClass
  { -- | all `extends` appeared in the direct class scope (i.e. super classes),
    --  up to time of analysis
    el'class'exts'wip :: !(TVar [EL'AttrRef]),
    -- | all `extends` appeared in nested (method) scopes (i.e. super objects),
    --  up to time of analysis
    el'inst'exts'wip :: !(TVar [EL'AttrRef]),
    -- | 1st appearances of exported artifacts in the direct class scope (i.e.
    -- class exports), up to time of analysis
    el'class'exps'wip :: !(IOPD AttrKey EL'AttrDef),
    -- | 1st appearances of exported artifacts in nested (method) scopes (i.e.
    -- object exports), up to time of analysis
    el'inst'exps'wip :: !(IOPD AttrKey EL'AttrDef)
  }

-- a method procedure, including vanilla method, generator, producer, operator,
-- (vanilla/generator/producer) arrow, and maybe a bit confusing, scoped blocks
data EL'RunProc = EL'RunProc
  { -- | redundant to `el'modu'exts'wip` or `el'obj'exts'wip` or
    -- `el'class'exts'wip` or `el'inst'exts'wip` whichever is appropriate
    el'scope'exts'wip :: !(TVar [EL'AttrRef]),
    -- | redundant to `el'modu'exps'wip` or `el'obj'exps'wip` or
    -- `el'class'exps'wip` or `el'inst'exps'wip` whichever is appropriate
    el'scope'exps'wip :: !EL'Exports,
    -- | last appearances of attributes encountered, up to time of analysis
    el'scope'attrs'wip :: !(IOPD AttrKey EL'AttrDef),
    -- | 1st appearances of effectful artifacts, up to time of analysis
    el'scope'effs'wip :: !(IOPD AttrKey EL'AttrDef),
    -- | last appearances of annotations encountered in the direct class scope,
    -- up to time of analysis
    el'scope'annos'wip :: !(IOPD AttrKey EL'AttrAnno),
    -- | end position for current region in the scope, known lately
    el'scope'end'wip :: !(TVar SrcPos),
    -- | accumulated sections lately
    el'scope'secs'wip :: !(TVar [EL'Section]),
    -- | accumulated symbols lately
    el'scope'symbols'wip :: !(TVar [EL'AttrSym])
  }

el'RunTx :: EL'AnalysisState -> EL'Tx -> STM ()
el'RunTx !eas !act = act eas
{-# INLINE el'RunTx #-}

el'ExitTx :: EL'TxExit a -> a -> EL'Tx
el'ExitTx !exit !a !eas = exit a eas
{-# INLINE el'ExitTx #-}

el'Exit :: EL'AnalysisState -> EL'TxExit a -> a -> STM ()
el'Exit !eas !exit !a = exit a eas
{-# INLINE el'Exit #-}
