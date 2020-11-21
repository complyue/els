module Language.Edh.LS.Analyze where

import Control.Concurrent.STM
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import qualified Data.Map.Strict as TreeMap
import Data.Text (Text)
import qualified Data.Text as T
import Language.Edh.EHI
import Language.Edh.Evaluate
import Language.Edh.LS.RtTypes
import Language.Edh.Meta.Model
import System.FilePath
import Prelude

el'RunAnalysis :: EL'World -> EL'Analysis -> EdhTx -> EdhTx
el'RunAnalysis !elw !ana !anaExit !ets = ana done elw ets
  where
    !pmav = el'modu'acts elw

    done _ets =
      swapTVar pmav Map.empty >>= \ !pmas ->
        if Map.null pmas
          then anaExit ets
          else driveAnalysis $ Map.toList pmas

    driveAnalysis :: [(EL'ModuRef, TVar [EL'ModuleAction])] -> STM ()
    driveAnalysis [] = done ets
    driveAnalysis ((EL'ModuRef !home !modu'name, !varActs) : rest) =
      -- XXX
      driveAnalysis rest

el'ResolveModule :: Text -> (EL'ModuRef -> EL'Act) -> EL'Act
el'ResolveModule !moduFile !exit !elw !ets =
  el'RunAct elw ets $
    exit
      -- XXX
      undefined

el'WithModule :: EL'ModuRef -> EL'ModuleAction -> EL'Act
el'WithModule !mref !act !elw _ets = do
  !am <- readTVar mav
  case Map.lookup mref am of
    Nothing -> newTVar [act] >>= \ !av -> writeTVar mav $ Map.insert mref av am
    Just !av -> modifyTVar' av (act :)
  where
    !mav = el'modu'acts elw
