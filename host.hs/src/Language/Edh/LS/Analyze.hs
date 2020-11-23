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
el'RunAnalysis !elw !ana !anaExit !ets =
  newTVar [ana] >>= \ !pas ->
    driveEdhAnalysis anaExit (EL'AnalysisState elw pas ets)

el'Postpone :: EL'Analysis -> EL'Tx
el'Postpone !act !eas = modifyTVar' (el'post'actions eas) (act :)

driveEdhAnalysis :: EdhTx -> EL'Tx
driveEdhAnalysis !anaExit eas@(EL'AnalysisState _elw !pas !ets) = checkDone
  where
    checkDone :: STM ()
    checkDone =
      swapTVar pas [] >>= \case
        [] -> anaExit ets
        !acts -> driveActions acts
    driveActions :: [EL'Analysis] -> STM ()
    driveActions [] = checkDone
    driveActions (act : rest) = act (const $ driveActions rest) eas

el'WithResolvedModule :: EL'ModuSlot -> (EL'ResolvedModule -> EL'Analysis) -> EL'TxExit -> EL'Tx
el'WithResolvedModule !ms !ana !anaExit = advanceStage anaExit
  where
    advanceStage :: EL'Analysis
    advanceStage !exit !eas =
      readTVar (el'modu'stage ms) >>= \case
        -- TODO these are still wrong
        EL'ModuParsed !parsed -> do
          el'Postpone advanceStage eas
          el'LoadModule parsed ms exit eas
        EL'ModuLoaded !loaded -> do
          el'Postpone advanceStage eas
          el'ResolveModule loaded ms exit eas
        EL'ModuResolved !resolved -> ana resolved anaExit eas
        EL'ModuFailed !exv -> edhThrow ets exv
      where
        !ets = el'ets eas

el'ResolveModule :: EL'LoadedModule -> EL'ModuSlot -> EL'Analysis
el'ResolveModule (EL'LoadedModule !arts !exps) !ms !exit !eas = do
  resolved@EL'ResolvedModule {} <- undefined -- XXX
  writeTVar (el'modu'stage ms) (EL'ModuResolved resolved)
  exit ets
  where
    !ets = el'ets eas

el'LoadModule :: EL'ParsedModule -> EL'ModuSlot -> EL'Analysis
el'LoadModule (EL'ParsedModule !stmts _diags) !ms !exit !eas = do
  loaded@EL'LoadedModule {} <- undefined -- XXX
  writeTVar (el'modu'stage ms) (EL'ModuLoaded loaded)
  exit ets
  where
    !ets = el'ets eas

el'LocateModule :: Text -> (EL'ModuSlot -> EL'Tx) -> EL'Tx
el'LocateModule !moduFile !exit eas@(EL'AnalysisState !elw !mps !ets) =
  el'RunTx eas $ exit undefined
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
