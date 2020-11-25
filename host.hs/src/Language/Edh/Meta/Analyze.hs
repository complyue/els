module Language.Edh.Meta.Analyze where

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import qualified Data.ByteString as B
import Data.Dynamic
import qualified Data.HashMap.Strict as Map
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (Decoding (Some), streamDecodeUtf8With)
import Data.Text.Encoding.Error (lenientDecode)
import qualified Data.Vector as V
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.EHI
import Language.Edh.Meta.Model
import Language.Edh.Meta.RtTypes
import Numeric.Search.Range
import System.Directory
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
  if not $ ".edh" `T.isSuffixOf` moduFile
    then throwEdh ets UsageError $ "Not a .edh file: " <> moduFile
    else
      runEdhTx ets $
        edhContIO $
          fsSearch >>= \case
            Left !err -> atomically $ throwEdh ets UsageError err
            Right (Left (!homePath, !scriptName, !relPath, !absFile)) ->
              atomically (prepareHome homePath)
                -- with 2 separate STM txs
                >>= atomically . goWith scriptName relPath absFile el'home'scripts
            Right (Right (!homePath, !moduName, !relPath, !absFile)) ->
              atomically (prepareHome homePath)
                -- with 2 separate STM txs
                >>= atomically . goWith moduName relPath absFile el'home'modules
  where
    goWith ::
      Text ->
      Text ->
      Text ->
      (EL'Home -> TMVar (Map.HashMap ModuleName EL'ModuSlot)) ->
      EL'Home ->
      STM ()
    goWith !name !relPath !absFile !mmField !home =
      takeTMVar mmVar >>= \ !mm ->
        case Map.lookup name mm of
          Just !ms ->
            let SrcDoc !prevDoc = el'modu'doc ms
             in if prevDoc /= absFile
                  then
                    throwEdh ets EvalError $
                      "bug: conflicting module located "
                        <> prevDoc
                        <> " vs "
                        <> absFile
                  else do
                    putTMVar mmVar mm
                    el'Exit eas exit ms
          Nothing -> do
            !parsed <- newEmptyTMVar
            !loaded <- newEmptyTMVar
            !resolved <- newEmptyTMVar
            !dependants <- newTVar Map.empty
            !dependencies <- newTVar Map.empty
            let !ms =
                  EL'ModuSlot
                    home
                    relPath
                    (SrcDoc absFile)
                    parsed
                    loaded
                    resolved
                    dependants
                    dependencies
            putTMVar mmVar (Map.insert name ms mm)
            el'Exit eas exit ms
      where
        !mmVar = mmField home

    prepareHome :: Text -> STM EL'Home
    prepareHome !homePath = do
      !homesVec <- takeTMVar (el'homes elw)
      let newHome (vPre, vPost) = do
            !modus <- newTMVar Map.empty
            !scripts <- newTMVar Map.empty
            let !home = EL'Home homePath modus scripts
            putTMVar (el'homes elw) $ V.force $ vPre V.++ V.cons home vPost
            return home
      case searchFromTo
        ( \ !i ->
            el'home'path (V.unsafeIndex homesVec i) >= homePath
        )
        0
        (V.length homesVec - 1) of
        Just !homeIdx ->
          let !home = V.unsafeIndex homesVec homeIdx
           in if homePath == el'home'path home
                then putTMVar (el'homes elw) homesVec >> return home
                else newHome $ V.splitAt homeIdx homesVec
        _ -> newHome (homesVec, V.empty)

    fsSearch ::
      IO
        ( Either
            Text
            ( Either
                (Text, ScriptName, Text, Text)
                (Text, ModuleName, Text, Text)
            )
        )
    fsSearch =
      canonicalizePath (T.unpack moduFile) >>= \ !absFile ->
        let go ::
              (FilePath, FilePath) ->
              IO
                ( Either
                    Text
                    ( Either
                        (Text, ScriptName, Text, Text)
                        (Text, ModuleName, Text, Text)
                    )
                )
            go (!dir, !relPath) = case splitFileName dir of
              (!homeDir, "edh_modules") -> case splitFileName relPath of
                (!moduName, "__main__.edh") ->
                  return $
                    Right $
                      Left
                        ( T.pack homeDir,
                          T.pack moduName,
                          T.pack (dir </> moduName),
                          T.pack absFile
                        )
                (!moduName, "__init__.edh") ->
                  let !conflictingFile = dir </> moduName <> ".edh"
                   in doesPathExist conflictingFile >>= \case
                        True ->
                          return $
                            Left $
                              "conflicting "
                                <> T.pack conflictingFile
                        False ->
                          return $
                            Right $
                              Right
                                ( T.pack homeDir,
                                  T.pack moduName,
                                  T.pack (dir </> moduName),
                                  T.pack absFile
                                )
                _ ->
                  let !moduName =
                        fromMaybe relPath $
                          stripExtension
                            ".edh"
                            relPath
                      !conflictingFile = dir </> moduName </> "__init__.edh"
                   in doesPathExist conflictingFile >>= \case
                        True ->
                          return $
                            Left $
                              "conflicting "
                                <> T.pack conflictingFile
                        False ->
                          return $
                            Right $
                              Right
                                ( T.pack homeDir,
                                  fromJust $
                                    T.stripSuffix ".edh" $
                                      T.pack
                                        relPath,
                                  T.pack (takeDirectory relPath),
                                  T.pack absFile
                                )
              (!gpdir, !pdir) ->
                doesDirectoryExist (dir </> "edh_modules") >>= \case
                  False ->
                    if gpdir == dir -- reached fs root
                      then return $ Left "not in any edh home"
                      else go (gpdir, pdir </> relPath)
                  True ->
                    return $
                      Right $
                        Left
                          ( T.pack dir,
                            T.pack relPath,
                            T.pack (takeDirectory relPath),
                            T.pack absFile
                          )
         in go $ splitFileName absFile

el'LocateImportee ::
  EL'ModuSlot ->
  Text ->
  EL'Analysis (Either Text EL'ModuSlot)
el'LocateImportee !msFrom !impSpec !exit !eas =
  if "." `T.isPrefixOf` impSpec
    then
      if null relPath
        then
          el'Exit eas exit $
            Left $ "can not do relative import from " <> fromFile
        else
          unsafeIOToSTM (findRelImport nomSpec) >>= \case
            Left !err -> el'Exit eas exit $ Left err
            Right !moduFile -> el'RunTx eas $
              el'LocateModule moduFile $ \ !ms ->
                el'ExitTx exit $ Right ms
    else
      unsafeIOToSTM
        (findAbsImport $ T.unpack $ el'home'path $ el'modu'home msFrom)
        >>= \case
          Left !err -> el'Exit eas exit $ Left err
          Right !moduFile -> el'RunTx eas $
            el'LocateModule moduFile $ \ !ms ->
              el'ExitTx exit $ Right ms
  where
    relPath = T.unpack $ el'modu'rel'base msFrom
    SrcDoc fromFile = el'modu'doc msFrom
    !nomSpec = T.unpack $ normalizeImpSpec impSpec
    normalizeImpSpec :: Text -> Text
    normalizeImpSpec = withoutLeadingSlash . withoutTrailingSlash
    withoutLeadingSlash spec = fromMaybe spec $ T.stripPrefix "/" spec
    withoutTrailingSlash spec = fromMaybe spec $ T.stripSuffix "/" spec

    findRelImport :: FilePath -> IO (Either Text Text)
    findRelImport !relImp = do
      !nomPath <- canonicalizePath $ relPath </> relImp
      let !edhFilePath = nomPath <> ".edh"
      doesFileExist edhFilePath >>= \case
        True -> return $ Right $ T.pack edhFilePath
        False ->
          let !edhIdxPath = nomPath </> "__init__.edh"
           in doesFileExist edhIdxPath >>= \case
                True -> return $ Right $ T.pack edhIdxPath
                False ->
                  return $
                    Left $
                      "no such module: " <> T.pack (show relImp)
                        <> " relative to: "
                        <> T.pack relPath

    findAbsImport :: FilePath -> IO (Either Text Text)
    findAbsImport !absPkgPath =
      let !emsDir = absPkgPath </> "edh_modules"
       in doesDirectoryExist emsDir >>= \case
            False -> tryParentDir
            True -> do
              let !nomPath = emsDir </> nomSpec
                  !edhFilePath = nomPath <> ".edh"
              doesFileExist edhFilePath >>= \case
                True ->
                  return $ Right $ T.pack edhFilePath
                False -> do
                  let !edhIdxPath = nomPath </> "__init__.edh"
                  doesFileExist edhIdxPath >>= \case
                    True ->
                      return $ Right $ T.pack edhIdxPath
                    False -> tryParentDir
      where
        tryParentDir =
          let !parentPkgPath = takeDirectory absPkgPath
           in if equalFilePath parentPkgPath absPkgPath
                then return $ Left $ "no such module: " <> T.pack (show nomSpec)
                else findAbsImport parentPkgPath

el'DoParseModule ::
  EL'ModuSlot ->
  TMVar EL'ParsedModule ->
  EL'TxExit () ->
  EL'Tx
el'DoParseModule !ms !pmVar !exit eas@(EL'AnalysisState _elw !ets) =
  unsafeIOToSTM
    ( streamDecodeUtf8With lenientDecode
        <$> B.readFile
          ( T.unpack
              moduFile
          )
    )
    >>= \case
      Some !moduSource _ _ ->
        parseEdh world moduFile moduSource >>= \case
          Left !err -> do
            let !msg = T.pack $ errorBundlePretty err
                !edhWrapException = edh'exception'wrapper world
                !edhErr =
                  EdhError ParseError msg (toDyn nil) $
                    getEdhErrCtx
                      0
                      ets
            edhWrapException (toException edhErr)
              >>= \ !exo -> edhThrow ets (EdhObject exo)
          Right (!stmts, _docCmt) -> do
            let !parsed = EL'ParsedModule stmts []
            void $ tryPutTMVar pmVar parsed
            el'Exit eas exit ()
  where
    !world = edh'prog'world $ edh'thread'prog ets
    SrcDoc !moduFile = el'modu'doc ms

el'DoLoadModule ::
  EL'ModuSlot ->
  EL'ParsedModule ->
  TMVar EL'LoadedModule ->
  EL'TxExit () ->
  EL'Tx
el'DoLoadModule
  !ms
  (EL'ParsedModule !stmts _parse'diags)
  !lmVar
  !exit
  eas@(EL'AnalysisState !elw !ets) = do
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
  eas@(EL'AnalysisState !elw !ets) = do
    let !resolved = undefined -- XXX
    void $ tryPutTMVar lmVar resolved
    el'Exit eas exit ()
