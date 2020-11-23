module Language.Edh.LS.Analyze where

import Control.Concurrent.STM
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import qualified Data.Map.Strict as TreeMap
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Language.Edh.EHI
import Language.Edh.Evaluate
import Language.Edh.LS.RtTypes
import Language.Edh.Meta.Model
import Numeric.Search.Range
import System.FilePath
import Prelude

el'RunAnalysis :: EL'World -> EL'Analysis -> EdhTx -> EdhTx
el'RunAnalysis !elw !ana !anaExit !ets = do
  !mps <- newTVar Map.empty
  let doneChk :: STM ()
      doneChk =
        swapTVar mps Map.empty >>= \ !mpm ->
          if Map.null mpm
            then anaExit ets
            else driveAnalysis $ Map.toList mpm
      driveAnalysis :: [(EL'ModuRef, TVar [EL'ModuProc])] -> STM ()
      driveAnalysis [] = doneChk
      driveAnalysis ((EL'ModuRef !home !modu'name, !varTxs) : rest) =
        -- XXX
        driveAnalysis rest
  ana (const doneChk) (EL'AnalysisState elw mps ets)

el'ResolveModule :: Text -> (Maybe EL'ModuRef -> EL'Tx) -> EL'Tx
el'ResolveModule !moduFile !exit eas@(EL'AnalysisState !elw !mps !ets) =
  el'RunTx eas $ exit Nothing
  where
    !moduHomeDir = moduFile

    !homesVar = el'homes elw

    getHome :: STM ()
    getHome = do
      !homesVec <- takeTMVar homesVar
      let !homeIdx =
            searchFromTo
              ( \ !i ->
                  el'home'path (V.unsafeIndex homesVec i) >= moduHomeDir
              )
              0
              (V.length homesVec - 1)
      return ()

el'WithModule :: EL'ModuRef -> EL'ModuProc -> EL'Tx
el'WithModule !mref !act eas@(EL'AnalysisState _elw !mps _ets) = do
  !mpm <- readTVar mps
  case Map.lookup mref mpm of
    Nothing -> newTVar [act] >>= \ !av -> writeTVar mps $ Map.insert mref av mpm
    Just !av -> modifyTVar' av (act :)