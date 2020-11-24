module Language.Edh.Meta.Analyze where

import Control.Concurrent.STM
import Control.Monad
import qualified Data.HashMap.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Language.Edh.EHI
import Language.Edh.Meta.Model
import Language.Edh.Meta.RtTypes
import Numeric.Search.Range
import System.FilePath
import Prelude

el'InvalidateModule :: Bool -> EL'ModuSlot -> EdhTxExit () -> EdhTx
el'InvalidateModule !srcChanged !ms !exit !ets = do
  when srcChanged $ do
    void $ tryTakeTMVar $ el'modu'parsed ms
    void $ tryTakeTMVar $ el'modu'loaded ms
  void $ tryTakeTMVar $ el'modu'resolved ms
  writeTVar (el'modu'dependencies ms) Map.empty
  readTVar (el'modu'dependants ms) >>= invalidateDependants [] . Map.toList
  where
    invalidateDependants ::
      [(EL'ModuSlot, Bool)] ->
      [(EL'ModuSlot, Bool)] ->
      STM ()
    invalidateDependants !upds [] = do
      unless (null upds) $
        modifyTVar' (el'modu'dependants ms) $ Map.union (Map.fromList upds)
      exitEdh ets exit ()
    invalidateDependants !upds ((!dependant, !hold) : rest) =
      Map.lookup ms {- HLINT ignore "Redundant <$>" -}
        <$> readTVar (el'modu'dependencies dependant) >>= \case
          Just True ->
            runEdhTx ets $
              el'InvalidateModule False dependant $ \_ _ets ->
                invalidateDependants upds rest
          _ ->
            if hold
              then invalidateDependants ((dependant, False) : upds) rest
              else invalidateDependants upds rest

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
                          ( \ !exitTry !etsTry ->
                              el'RunTx eas {el'ets = etsTry} $
                                el'DoResolveModule ms pm lm rmVar $ \() _eas ->
                                  exitEdh etsTry exitTry nil
                          )
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
                      ( edhCatchTx
                          ( \ !exitTry !etsTry ->
                              el'RunTx eas {el'ets = etsTry} $
                                el'DoLoadModule ms pm lmVar $ \() _eas ->
                                  exitEdh etsTry exitTry nil
                          )
                          endOfEdh
                          $ \ !recover !rethrow !etsCatching ->
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
                  ( edhCatchTx
                      ( \ !exitTry !etsTry ->
                          el'RunTx eas {el'ets = etsTry} $
                            el'DoParseModule ms pmVar $ \() _eas ->
                              exitEdh etsTry exitTry nil
                      )
                      endOfEdh
                      $ \ !recover !rethrow !etsCatching ->
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

el'LocateModule :: Text -> EL'TxExit EL'ModuSlot -> EL'Tx
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

el'DoParseModule ::
  EL'ModuSlot ->
  TMVar EL'ParsedModule ->
  EL'TxExit () ->
  EL'Tx
el'DoParseModule !ms !pmVar !exit !eas = do
  void $ tryPutTMVar pmVar undefined -- XXX
  el'Exit eas exit ()

el'DoLoadModule ::
  EL'ModuSlot ->
  EL'ParsedModule ->
  TMVar EL'LoadedModule ->
  EL'TxExit () ->
  EL'Tx
el'DoLoadModule !ms (EL'ParsedModule !stmts _parse'diags) !lmVar !exit !eas = do
  let !loaded = undefined -- XXX
  void $ tryPutTMVar lmVar loaded
  el'Exit eas exit ()

el'DoResolveModule ::
  EL'ModuSlot ->
  EL'ParsedModule ->
  EL'LoadedModule ->
  TMVar EL'ResolvedModule ->
  EL'TxExit () ->
  EL'Tx
el'DoResolveModule
  !ms
  (EL'ParsedModule !stmts _parse'diags)
  (EL'LoadedModule !arts !exps _load'diags)
  !lmVar
  !exit
  !eas = do
    let !resolved = undefined -- XXX
    void $ tryPutTMVar lmVar resolved
    el'Exit eas exit ()
