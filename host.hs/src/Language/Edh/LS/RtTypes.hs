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
  { -- use a tree map from absolute path to home record, so entry appears
    -- earlier is shallower
    el'homes :: !(TMVar (TreeMap.Map Text EL'Home)),
    el'modu'acts :: !(TVar (Map.HashMap EL'ModuRef (TVar [EL'ModuleAction])))
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

type EL'ModuleAction = EL'ModuSlot -> EL'Analysis

type EL'Analysis = EL'ActExit -> EL'Act

type EL'Act = EL'World -> EdhTx

type EL'ActExit = EdhTx

el'RunAct :: EL'World -> EdhThreadState -> EL'Act -> STM ()
el'RunAct !elw !ets !p = p elw ets
{-# INLINE el'RunAct #-}

el'ExitAct :: EL'ActExit -> EdhTx
el'ExitAct = id
{-# INLINE el'ExitAct #-}

el'Exit :: EdhThreadState -> EL'ActExit -> STM ()
el'Exit !ets !exit = exit ets
{-# INLINE el'Exit #-}
