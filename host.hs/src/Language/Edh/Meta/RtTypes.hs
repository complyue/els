module Language.Edh.Meta.RtTypes where

import Control.Concurrent.STM
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

el'AnalyzeModule ::
  EL'World ->
  EL'ModuSlot ->
  EL'Analysis a ->
  EL'TxExit a ->
  EdhTx
el'AnalyzeModule !elw !ms !ana !exit !ets = do
  !ctx'diags <- newTVar []
  !scope'attrs <- iopdEmpty
  !scope'effs <- iopdEmpty
  !scope'annos <- iopdEmpty
  !scope'end <- newTVar beginningSrcPos
  !secs <- newTVar []
  !scope'symbols <- newTVar []

  !exts <- newTVar []
  !exps <- iopdEmpty

  el'RunTx
    ( EL'AnalysisState
        elw
        EL'Context
          { el'ctx'module = ms,
            el'ctx'diags = ctx'diags,
            el'ctx'scope =
              EL'ObjectWIP
                EL'InitObject
                  { el'obj'exts'wip = exts,
                    el'obj'exps'wip = exps
                  }
                EL'RunProc
                  { el'scope'attrs'wip = scope'attrs,
                    el'scope'effs'wip = scope'effs,
                    el'scope'annos'wip = scope'annos,
                    el'scope'end'wip = scope'end,
                    el'scope'secs'wip = secs,
                    el'scope'symbols'wip = scope'symbols
                  },
            el'ctx'outers = [],
            el'ctx'pure = False,
            el'ctx'exporting = False,
            el'ctx'eff'defining = False
          }
        ets
    )
    (ana exit)

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
  { -- | the context module
    el'ctx'module :: !EL'ModuSlot,
    el'ctx'diags :: !(TVar [EL'Diagnostic]),
    --

    -- | current scope work-in-progress
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
    el'ctx'eff'defining :: !Bool
  }

data EL'ScopeWIP
  = EL'ProcWIP !EL'RunProc
  | EL'ClassWIP !EL'DefineClass !EL'RunProc
  | EL'ObjectWIP !EL'InitObject !EL'RunProc

el'wip'proc :: EL'ScopeWIP -> EL'RunProc
el'wip'proc (EL'ProcWIP p) = p
el'wip'proc (EL'ClassWIP _ p) = p
el'wip'proc (EL'ObjectWIP _ p) = p

-- | an object initializing procedure, can be a module procedure or namespace
-- procedure
data EL'InitObject = EL'InitObject
  { -- | all `extends` appeared in the direct scope and nested scopes (i.e.
    -- super objects),  up to time of analysis
    el'obj'exts'wip :: !(TVar [EL'AttrRef]),
    -- | 1st appearances of exported artifacts in the direct scope and nested
    -- (method) scopes (i.e. object exports), up to time of analysis
    el'obj'exps'wip :: !(IOPD AttrKey EL'AttrDef)
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
  { -- | last appearances of attributes encountered, up to time of analysis
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
