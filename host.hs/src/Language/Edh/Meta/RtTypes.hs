module Language.Edh.Meta.RtTypes where

import Control.Concurrent.STM
import Data.Text (Text)
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

el'RunAnalysis :: EL'World -> EL'ModuSlot -> EL'Analysis a -> EL'TxExit a -> EdhTx
el'RunAnalysis !elw !ms !ana !exit !ets = do
  !exts <- newTVar []
  !exps <- iopdEmpty
  !diags <- newTVar []
  !secs <- newTVar []
  !region'end <- newTVar beginningSrcPos
  !region'annos <- iopdEmpty
  !region'attrs <- iopdEmpty
  !region'effs <- iopdEmpty
  el'RunTx
    ( EL'AnalysisState
        elw
        EL'Context
          { el'ctx'module = ms,
            el'ctx'scope =
              EL'ScopeWIP
                { el'scope'is'class'wip = False,
                  el'scope'exts'wip = exts,
                  el'scope'exps'wip = exps,
                  el'scope'diags'wip = diags,
                  el'scope'secs'wip = secs,
                  el'region'end'wip = region'end,
                  el'region'annos'wip = region'annos,
                  el'region'attrs'wip = region'attrs,
                  el'region'effs'wip = region'effs
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

data EL'Context = EL'Context
  { -- | the context module
    el'ctx'module :: !EL'ModuSlot,
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

data EL'ScopeWIP = EL'ScopeWIP
  { -- | if this scope wip is for a class
    el'scope'is'class'wip :: !Bool,
    -- | all `extends` (i.e. super objects) appeared lately
    el'scope'exts'wip :: !(TVar [EL'Value]),
    -- | exported artifacts lately
    el'scope'exps'wip :: !(IOPD EL'AttrKey EL'Value),
    -- | diagnostics generated lately
    el'scope'diags'wip :: !(TVar [(SrcRange, Text)]),
    --

    -- | accumulated sections lately
    el'scope'secs'wip :: !(TVar [EL'Section]),
    -- | latest end position known lately
    el'region'end'wip :: !(TVar SrcPos),
    -- | all annotations encountered lately
    el'region'annos'wip :: !(IOPD EL'AttrKey EL'Value),
    -- | all attributes encountered lately
    el'region'attrs'wip :: !(IOPD EL'AttrKey EL'Value),
    -- | all effectful artifacts encountered lately
    el'region'effs'wip :: !(IOPD EL'AttrKey EL'Value)
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

data EL'TopLevels = EL'TopLevels
  { -- | toplevel artifacts defined
    el'top'arts :: !(IOPD EL'AttrKey EL'Value),
    -- | all `extends` (i.e. super objects) appeared at toplevel
    el'top'exts :: !(TVar [EL'Value]),
    -- | exported artifacts at toplevel
    el'top'exps :: !(IOPD EL'AttrKey EL'Value),
    -- | diagnostics generated during analyzing
    el'top'diags :: !(TVar [(SrcRange, Text)])
  }
