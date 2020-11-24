module Language.Edh.LS.RtTypes where

import Control.Concurrent.STM
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.Hashable
import qualified Data.Map.Strict as TreeMap
import Data.Text (Text)
import qualified Data.Text as T
import Data.Vector (Vector)
import qualified Data.Vector as V
import Language.Edh.EHI
import Language.Edh.Evaluate
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

el'RunAnalysis :: EL'World -> EL'Analysis a -> EL'TxExit a -> EdhTx
el'RunAnalysis !elw !ana !exit !ets =
  el'RunTx (EL'AnalysisState elw ets) (ana exit)

type EL'Analysis a = EL'TxExit a -> EL'Tx

type EL'TxExit a = a -> EL'Tx

type EL'Tx = EL'AnalysisState -> STM ()

data EL'AnalysisState = EL'AnalysisState
  { el'world :: !EL'World,
    el'ets :: !EdhThreadState
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
