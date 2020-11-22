module Language.Edh.LS.RtTypes where

import Control.Concurrent.STM
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.Hashable
import qualified Data.Map.Strict as TreeMap
import Data.Text (Text)
import qualified Data.Text as T
import Language.Edh.EHI
import Language.Edh.Evaluate
import Language.Edh.Meta.Model
import Prelude

data EL'World = EL'World
  { -- use a tree map from absolute path to home record, so nested homes follow
    -- their respective parent
    el'homes :: !(TMVar (TreeMap.Map Text EL'Home)),
    -- | it's end-of-world if this sink goes eos
    el'announcements :: !EventSink
  }

data EL'ModuRef = EL'ModuRef
  { el'modu'ref'home :: !EL'Home,
    el'modu'ref'name :: !ModuleName
  }

instance Eq EL'ModuRef where
  (EL'ModuRef !x'home !x'modu'name) == (EL'ModuRef !y'home !y'modu'name) =
    x'home == y'home && x'modu'name == y'modu'name

instance Hashable EL'ModuRef where
  hashWithSalt s (EL'ModuRef (EL'Home home'path _home'modus) modu'name) =
    s `hashWithSalt` home'path `hashWithSalt` modu'name

type EL'ModuProc = EL'ModuSlot -> EL'Analysis

type EL'Analysis = EL'TxExit -> EL'Tx

type EL'TxExit = EdhTx

type EL'Tx = EL'AnalysisState -> STM ()

data EL'AnalysisState = EL'AnalysisState
  { el'world :: !EL'World,
    el'modu'procs :: !(TVar (Map.HashMap EL'ModuRef (TVar [EL'ModuProc]))),
    el'ets :: !EdhThreadState
  }

el'RunTx :: EL'AnalysisState -> EL'Tx -> STM ()
el'RunTx !eas !act = act eas
{-# INLINE el'RunTx #-}

el'ExitTx :: EL'TxExit -> EL'Tx
el'ExitTx !exit (EL'AnalysisState _elw _mprocs !ets) = exit ets
{-# INLINE el'ExitTx #-}

el'Exit :: EdhThreadState -> EL'TxExit -> STM ()
el'Exit !ets !exit = exit ets
{-# INLINE el'Exit #-}
