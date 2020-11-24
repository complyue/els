module Language.Edh.LS.Analyze where

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
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

el'RunAnalysis :: EL'World -> EL'Analysis a -> EL'TxExit a -> EdhTx
el'RunAnalysis !elw !ana !exit !ets =
  el'RunTx (EL'AnalysisState elw ets) (ana exit)

el'ResolveModule :: EL'ModuSlot -> EL'Analysis (TMVar EL'ResolvedModule)
el'ResolveModule !ms !exit = el'LoadModule ms $
  \ !lmVar -> el'ParseModule ms $ \ !pmVar !eas -> do
    !lm <- readTMVar lmVar
    !pm <- readTMVar pmVar
    let !mrVar = el'modu'resolved ms
        goResolve :: STM ()
        goResolve =
          tryReadTMVar mrVar >>= \case
            Just !rmVar -> el'Exit eas exit rmVar
            Nothing -> do
              !rmVar <- newEmptyTMVar
              tryPutTMVar mrVar rmVar >>= \case
                False -> goResolve
                True -> do
                  runEdhTx (el'ets eas) $
                    forkEdh
                      id
                      ( edhCatchTx
                          (el'DoResolveModule ms pm lm rmVar)
                          endOfEdh
                          $ \ !recover !rethrow !etsCatching ->
                            case edh'ctx'match $ edh'context etsCatching of
                              EdhNil -> do
                                void $ -- in case it's not filled
                                  tryPutTMVar rmVar $
                                    EL'ResolvedModule
                                      (EL'Scope noSrcRange V.empty)
                                      odEmpty
                                      [ (noSrcRange, "<no-load>")
                                      ]
                                runEdhTx etsCatching $ rethrow nil
                              !exv -> edhValueDesc etsCatching exv $
                                \ !exDesc -> do
                                  void $ -- in case it's not filled
                                    tryPutTMVar rmVar $
                                      EL'ResolvedModule
                                        (EL'Scope noSrcRange V.empty)
                                        odEmpty
                                        [ (noSrcRange, exDesc)
                                        ]
                                  runEdhTx etsCatching $ recover nil
                      )
                      endOfEdh
                  el'Exit eas exit rmVar
    goResolve

el'LoadModule :: EL'ModuSlot -> EL'Analysis (TMVar EL'LoadedModule)
el'LoadModule !ms !exit = el'ParseModule ms $ \ !pmVar !eas ->
  readTMVar pmVar >>= \ !pm ->
    let !mlVar = el'modu'loaded ms
        goLoad :: STM ()
        goLoad =
          tryReadTMVar mlVar >>= \case
            Just !lmVar -> el'Exit eas exit lmVar
            Nothing -> do
              !lmVar <- newEmptyTMVar
              tryPutTMVar mlVar lmVar >>= \case
                False -> goLoad
                True -> do
                  runEdhTx (el'ets eas) $
                    forkEdh
                      id
                      ( edhCatchTx (el'DoLoadModule ms pm lmVar) endOfEdh $
                          \ !recover !rethrow !etsCatching ->
                            case edh'ctx'match $ edh'context etsCatching of
                              EdhNil -> do
                                void $ -- in case it's not filled
                                  tryPutTMVar lmVar $
                                    EL'LoadedModule
                                      odEmpty
                                      odEmpty
                                      [ (noSrcRange, "<no-load>")
                                      ]
                                runEdhTx etsCatching $ rethrow nil
                              !exv -> edhValueDesc etsCatching exv $
                                \ !exDesc -> do
                                  void $ -- in case it's not filled
                                    tryPutTMVar lmVar $
                                      EL'LoadedModule
                                        odEmpty
                                        odEmpty
                                        [ (noSrcRange, exDesc)
                                        ]
                                  runEdhTx etsCatching $ recover nil
                      )
                      endOfEdh
                  el'Exit eas exit lmVar
     in goLoad

el'ParseModule :: EL'ModuSlot -> EL'Analysis (TMVar EL'ParsedModule)
el'ParseModule !ms !exit !eas = goParse
  where
    !mpVar = el'modu'parsed ms
    goParse :: STM ()
    goParse =
      tryReadTMVar mpVar >>= \case
        Just !pmVar -> el'Exit eas exit pmVar
        Nothing -> do
          !pmVar <- newEmptyTMVar
          tryPutTMVar mpVar pmVar >>= \case
            False -> goParse
            True -> do
              runEdhTx (el'ets eas) $
                forkEdh
                  id
                  ( edhCatchTx (el'DoParseModule ms pmVar) endOfEdh $
                      \ !recover !rethrow !etsCatching ->
                        case edh'ctx'match $ edh'context etsCatching of
                          EdhNil -> do
                            void $ -- in case it's not filled
                              tryPutTMVar pmVar $
                                EL'ParsedModule
                                  []
                                  [ (noSrcRange, "<no-parse>")
                                  ]
                            runEdhTx etsCatching $ rethrow nil
                          !exv -> edhValueDesc etsCatching exv $ \ !exDesc -> do
                            void $ -- in case it's not filled
                              tryPutTMVar pmVar $
                                EL'ParsedModule
                                  []
                                  [ (noSrcRange, exDesc)
                                  ]
                            runEdhTx etsCatching $ recover nil
                  )
                  endOfEdh
              el'Exit eas exit pmVar

el'LocateModule :: Text -> (EL'ModuSlot -> EL'Tx) -> EL'Tx
el'LocateModule !moduFile !exit eas@(EL'AnalysisState !elw !ets) =
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

el'DoParseModule :: EL'ModuSlot -> TMVar EL'ParsedModule -> EdhTxExit -> EdhTx
el'DoParseModule !ms !pmVar !exit !ets = do
  void $ tryPutTMVar pmVar undefined -- XXX
  exitEdh ets exit nil

el'DoLoadModule ::
  EL'ModuSlot ->
  EL'ParsedModule ->
  TMVar EL'LoadedModule ->
  EdhTxExit ->
  EdhTx
el'DoLoadModule !ms (EL'ParsedModule !stmts _parse'diags) !lmVar !exit !ets = do
  void $ tryPutTMVar lmVar undefined -- XXX
  exitEdh ets exit nil

el'DoResolveModule ::
  EL'ModuSlot ->
  EL'ParsedModule ->
  EL'LoadedModule ->
  TMVar EL'ResolvedModule ->
  EdhTxExit ->
  EdhTx
el'DoResolveModule
  !ms
  (EL'ParsedModule !stmts _parse'diags)
  (EL'LoadedModule !arts !exps _load'diags)
  !lmVar
  !exit
  !ets = do
    void $ tryPutTMVar lmVar undefined -- XXX
    exitEdh ets exit nil
