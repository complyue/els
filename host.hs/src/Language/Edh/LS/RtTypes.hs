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
    -- | it's end-of-world if this sink goes end-of-stream
    el'announcements :: !EventSink
  }

type EL'Analysis = EL'TxExit -> EL'Tx

type EL'TxExit = EdhTx

type EL'Tx = EL'AnalysisState -> STM ()

data EL'AnalysisState = EL'AnalysisState
  { el'world :: !EL'World,
    -- | actions scheduled to happen later, they'll be triggered in the reverse
    -- order as scheduled
    el'post'actions :: !(TVar [EL'Analysis]),
    el'ets :: !EdhThreadState
  }

el'RunTx :: EL'AnalysisState -> EL'Tx -> STM ()
el'RunTx !eas !act = act eas
{-# INLINE el'RunTx #-}

el'ExitTx :: EL'TxExit -> EL'Tx
el'ExitTx !exit !eas = exit $ el'ets eas
{-# INLINE el'ExitTx #-}

el'Exit :: EdhThreadState -> EL'TxExit -> STM ()
el'Exit !ets !exit = exit ets
{-# INLINE el'Exit #-}
