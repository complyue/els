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
el'RunAnalysis !elw !ms !ana !exit !ets =
  el'RunTx
    ( EL'AnalysisState
        elw
        EL'Context
          { el'ctx'module = ms,
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
  { el'ctx'module :: !EL'ModuSlot,
    el'ctx'pure :: !Bool,
    el'ctx'exporting :: !Bool,
    el'ctx'eff'defining :: !Bool
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
