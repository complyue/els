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

el'ResolveModule :: EL'Analysis (TMVar EL'ResolvedModule)
el'ResolveModule !exit !eas = el'RunTx eas $
  el'ParseModule $ \ !pmVar _eas -> do
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
                                el'DoResolveModule pm rmVar $ \() _eas ->
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
                                      [ (noSrcRange, "<no-load>")
                                      ]
                                runEdhTx etsCatching $ rethrow nil
                              !exv -> edhValueDesc etsCatching exv $
                                \ !exDesc -> do
                                  void $ -- in case it's not filled
                                    tryPutTMVar rmVar $
                                      EL'ResolvedModule
                                        (EL'Scope noSrcRange V.empty)
                                        [ (noSrcRange, exDesc)
                                        ]
                                  runEdhTx etsCatching $ recover nil
                      )
                      endOfEdh
                  el'Exit eas exit rmVar
    goResolve
  where
    eac = el'context eas
    ms = el'ctx'module eac

el'LoadModule :: EL'Analysis (TMVar EL'LoadedModule)
el'LoadModule !exit !eas = el'RunTx eas $
  el'ParseModule $ \ !pmVar _eas ->
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
                                  el'DoLoadModule pm lmVar $ \() _eas ->
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
  where
    eac = el'context eas
    ms = el'ctx'module eac

el'ParseModule :: EL'Analysis (TMVar EL'ParsedModule)
el'ParseModule !exit !eas = goParse
  where
    !mpVar = el'modu'parsed $ el'ctx'module $ el'context eas
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
                            el'DoParseModule pmVar $ \() _eas ->
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

el'LocateModule :: EL'World -> Text -> EdhProc EL'ModuSlot
el'LocateModule !elw !moduFile !exit !ets =
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
                    exitEdh ets exit ms
          Nothing -> do
            !parsed <- newEmptyTMVar
            !loaded <- newEmptyTMVar
            !resolved <- newEmptyTMVar
            !exports <- newEmptyTMVar
            !exps'upd <- newBroadcastTChan
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
                    exports
                    exps'upd
                    dependants
                    dependencies
            putTMVar mmVar (Map.insert name ms mm)
            exitEdh ets exit ms
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

el'LocateImportee :: Text -> EL'Analysis (Either Text EL'ModuSlot)
el'LocateImportee !impSpec !exit !eas =
  if "." `T.isPrefixOf` impSpec
    then
      if null relPath
        then
          el'Exit eas exit $
            Left $ "can not do relative import from " <> fromFile
        else
          unsafeIOToSTM (findRelImport nomSpec) >>= \case
            Left !err -> el'Exit eas exit $ Left err
            Right !moduFile -> runEdhTx ets $
              el'LocateModule elw moduFile $ \ !ms _ets ->
                el'Exit eas exit $ Right ms
    else
      unsafeIOToSTM
        (findAbsImport $ T.unpack $ el'home'path $ el'modu'home msFrom)
        >>= \case
          Left !err -> el'Exit eas exit $ Left err
          Right !moduFile -> runEdhTx ets $
            el'LocateModule elw moduFile $ \ !ms _ets ->
              el'Exit eas exit $ Right ms
  where
    elw = el'world eas
    ets = el'ets eas
    eac = el'context eas
    msFrom = el'ctx'module eac
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

el'DoParseModule :: TMVar EL'ParsedModule -> EL'Analysis ()
el'DoParseModule !pmVar !exit eas@(EL'AnalysisState _elw !eac !ets) =
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
    SrcDoc !moduFile = el'modu'doc $ el'ctx'module eac

el'DoLoadModule :: EL'ParsedModule -> TMVar EL'LoadedModule -> EL'Analysis ()
el'DoLoadModule (EL'ParsedModule !stmts _parse'diags) !lmVar !exit !eas = do
  !arts <- iopdEmpty {- HLINT ignore "Reduce duplication" -}
  !exts <- newTVar []
  !exps <- iopdEmpty
  !diags <- newTVar []
  let !tops = EL'TopLevels arts exts exps diags
  el'RunTx eas $
    el'LoadTopStmts
      tops
      stmts
      $ \_ _eas -> do
        !arts' <- iopdSnapshot arts
        !exps' <- iopdSnapshot exps
        !diags' <- readTVar diags
        let !loaded = EL'LoadedModule arts' exps' $! reverse diags'
        void $ tryPutTMVar lmVar loaded
        el'Exit eas exit ()

el'LoadTopStmts :: EL'TopLevels -> [StmtSrc] -> EL'Analysis EL'Value
el'LoadTopStmts !tops !stmts !exit !eas = go stmts
  where
    go :: [StmtSrc] -> STM ()
    go [] = el'Exit eas exit $ EL'Const nil
    go (stmt : rest) = el'RunTx eas $
      el'LoadTopStmt tops stmt $ \ !val _eas' -> case rest of
        [] -> el'Exit eas exit val
        _ -> go rest

el'LoadTopStmt :: EL'TopLevels -> StmtSrc -> EL'Analysis EL'Value
el'LoadTopStmt
  tops@(EL'TopLevels _arts !exts _exps !diags)
  (StmtSrc !stmt !stmt'span)
  !exit
  !eas = case stmt of
    ExprStmt !expr _docCmt ->
      el'RunTx eas $
        el'LoadTopExpr tops (ExprSrc expr stmt'span) exit
    LetStmt _argsRcvr _argsSndr -> do
      -- TODO recognize defines & exports
      el'Exit eas exit $ EL'Const nil
    ExtendsStmt !superExpr -> el'RunTx eas $
      el'LoadTopExpr tops superExpr $ \ !superVal _eas -> do
        case superVal of
          EL'Apk (EL'ArgsPack !supers !kwargs)
            | odNull kwargs ->
              modifyTVar' exts (++ supers)
          EL'Value {} ->
            -- TODO validate it really be an object
            modifyTVar' exts (++ [superVal])
          -- TODO elaborate the error msg
          _ -> modifyTVar' diags ((stmt'span, "invalid super") :)
        el'Exit eas exit $ EL'Const nil
    -- TODO recognize more stmts
    -- EffectStmt !effs !docCmt -> undefined
    _ -> el'Exit eas exit $ EL'Const nil

el'LoadTopExpr :: EL'TopLevels -> ExprSrc -> EL'Analysis EL'Value
el'LoadTopExpr
  tops@(EL'TopLevels _arts _exts !exps !diags)
  xsrc@(ExprSrc !expr _expr'span)
  !exit
  eas@(EL'AnalysisState _elw !eac !ets) = case expr of
    ExportExpr !expr' ->
      el'RunTx eas {el'context = (el'context eas) {el'ctx'exporting = True}} $
        el'LoadTopExpr tops expr' exit
    AtoIsoExpr !expr' ->
      el'RunTx eas $ el'LoadTopExpr tops expr' exit
    ParenExpr !expr' ->
      el'RunTx eas $ el'LoadTopExpr tops expr' exit
    ArgsPackExpr !argSenders ->
      el'RunTx eas $
        el'LoadTopApk tops argSenders $ exit . EL'Apk
    BlockExpr !stmts ->
      el'RunTx eas $ el'LoadTopStmts tops stmts exit
    IfExpr !cond !cseq !alt ->
      el'RunTx eas $
        el'LoadTopExpr tops cond $ \ !val _eas -> case val of
          EL'Const !constVal -> edhValueNull ets constVal $ \case
            False -> el'RunTx eas $ el'LoadTopStmt tops cseq exit
            True -> el'RunTx eas $ case alt of
              Nothing -> el'ExitTx exit $ EL'Const nil
              Just !elseStmt -> el'LoadTopStmt tops elseStmt exit
          _ -> el'RunTx eas $
            el'LoadTopStmt tops cseq $ \_ -> case alt of
              Nothing -> \_eas -> rtnParsed {- HLINT ignore "Use const" -}
              Just !elseStmt -> el'LoadTopStmt tops elseStmt $
                \_ _eas -> rtnParsed
    --

    -- procedure definitions
    MethodExpr HostDecl {} -> error "bug: host method declaration"
    MethodExpr (ProcDecl !nameAddr _ _ _) -> do
      !mthStageVar <- newTVar EL'ParsedValue
      let !mthKey = el'AttrKey nameAddr
          !mthVal =
            EL'Value
              ms
              xsrc
              mthStageVar
              (Just MethodType)
      when (el'ctx'exporting eac) $
        iopdInsert mthKey mthVal exps
      el'Exit eas exit mthVal
    GeneratorExpr HostDecl {} -> error "bug: host method declaration"
    GeneratorExpr (ProcDecl !nameAddr _ _ _) -> do
      !mthStageVar <- newTVar EL'ParsedValue
      let !mthKey = el'AttrKey nameAddr
          !mthVal =
            EL'Value
              ms
              xsrc
              mthStageVar
              (Just GeneratorType)
      when (el'ctx'exporting eac) $
        iopdInsert mthKey mthVal exps
      el'Exit eas exit mthVal
    InterpreterExpr HostDecl {} -> error "bug: host method declaration"
    InterpreterExpr (ProcDecl !nameAddr _ _ _) -> do
      !mthStageVar <- newTVar EL'ParsedValue
      let !mthKey = el'AttrKey nameAddr
          !mthVal =
            EL'Value
              ms
              xsrc
              mthStageVar
              (Just InterpreterType)
      when (el'ctx'exporting eac) $
        iopdInsert mthKey mthVal exps
      el'Exit eas exit mthVal
    ProducerExpr HostDecl {} -> error "bug: host method declaration"
    ProducerExpr (ProcDecl !nameAddr _ _ _) -> do
      !mthStageVar <- newTVar EL'ParsedValue
      let !mthKey = el'AttrKey nameAddr
          !mthVal =
            EL'Value
              ms
              xsrc
              mthStageVar
              (Just ProducerType)
      when (el'ctx'exporting eac) $
        iopdInsert mthKey mthVal exps
      el'Exit eas exit mthVal
    OpDefiExpr _opFixity _opPrec _opSym (ProcDecl !opAddr _ _ _) -> do
      !opStageVar <- newTVar EL'ParsedValue
      let !opKey = el'AttrKey opAddr
          !opVal =
            EL'Value
              ms
              xsrc
              opStageVar
              (Just OperatorType)
      when (el'ctx'exporting eac) $
        iopdInsert opKey opVal exps
      el'Exit eas exit opVal
    OpOvrdExpr _opFixity _opPrec _opSym (ProcDecl !opAddr _ _ _) -> do
      !opStageVar <- newTVar EL'ParsedValue
      let !opKey = el'AttrKey opAddr
          !opVal =
            EL'Value
              ms
              xsrc
              opStageVar
              (Just OperatorType)
      when (el'ctx'exporting eac) $
        iopdInsert opKey opVal exps
      el'Exit eas exit opVal
    --

    -- class definition
    ClassExpr HostDecl {} -> error "bug: host class declaration"
    ClassExpr (ProcDecl !nameAddr !argsRcvr !pbody _proc'loc) -> case argsRcvr of
      -- a normal class
      WildReceiver -> loadClass nameAddr odEmpty odEmpty pbody
      -- a data class (ADT)
      PackReceiver !ars -> do
        !dfArts <- recvDataClassFields ars
        loadClass nameAddr odEmpty dfArts pbody
      SingleReceiver !ar -> do
        !dfArts <- recvDataClassFields [ar]
        loadClass nameAddr odEmpty dfArts pbody

    -- namespace definition
    NamespaceExpr HostDecl {} _ -> error "bug: host ns declaration"
    NamespaceExpr
      ( ProcDecl
          nameAddr@(AttrAddrSrc _ name'span)
          _
          !pbody
          _proc'loc
        )
      !argSenders -> el'RunTx eas $
        el'LoadTopApk tops argSenders $ \(EL'ArgsPack !args !kwargs) ->
          el'LoadClass tops pbody $ \(!supers, !clsArts, !clsExps) _eas -> do
            unless (null args) $
              modifyTVar' diags ((name'span, "positional arg to namespace") :)
            let !clsKey = el'AttrKey nameAddr
                !clsStage =
                  EL'LoadedClass
                    clsKey
                    []
                    ( odFromList $ odToList kwargs ++ odToList clsArts
                    )
                    clsExps
            !clsStageVar <- newTVar clsStage
            let !clsVal = EL'Value ms xsrc clsStageVar Nothing
                !nsoStage = EL'LoadedObject clsVal supers
            !nsoStageVar <- newTVar nsoStage
            let !nsoVal = EL'Value ms xsrc nsoStageVar Nothing
            when (el'ctx'exporting eac) $
              iopdInsert clsKey nsoVal exps
            el'Exit eas exit nsoVal

    -- operator application, some carry assignment semantics
    InfixExpr !opSym (ExprSrc !lhExpr _lh'span) !rhExprSrc ->
      if "=" `T.isSuffixOf` opSym
        then -- handle operators do assignment i.e. (=), also (:=), and other
        case lhExpr of -- assignment-likes (+=) (-=) ...
          AttrExpr (DirectRef !addr) -> do
            !artStageVar <- newTVar EL'ParsedValue
            let !artKey = el'AttrKey addr
                !artVal =
                  EL'Value
                    ms
                    rhExprSrc
                    artStageVar
                    Nothing
            when (el'ctx'exporting eac) $
              iopdInsert artKey artVal exps
            el'Exit eas exit artVal
          _ -> rtnParsed
        else --
        -- if "::" == opSym --
        --   then -- annotation
        --     undefined
        --   else --
          rtnParsed
    --

    -- importing
    -- ImportExpr !argsRcvr !srcExpr !maybeInto ->
    --   -- TODO feasible to load re-exports during loading stage?
    --   undefined --

    -- TODO recognize more exprs
    -- CaseExpr !tgtExpr !branchesExpr -> undefined
    -- ForExpr !argsRcvr !iterExpr !doStmt -> undefined
    -- CallExpr !calleeExpr !argsSndr -> undefined
    _ -> rtnParsed
    where
      !ms = el'ctx'module eac
      rtnParsed = do
        !vstage <- newTVar EL'ParsedValue
        el'Exit eas exit $ EL'Value ms xsrc vstage Nothing

      loadClass ::
        AttrAddrSrc ->
        EL'Artifacts ->
        EL'Artifacts ->
        StmtSrc ->
        STM ()
      loadClass !nameAddr !preArts !postArts !pbody = el'RunTx eas $
        el'LoadClass tops pbody $ \(!supers, !clsArts, !clsExps) _eas -> do
          let !clsKey = el'AttrKey nameAddr
              !clsStage =
                EL'LoadedClass
                  clsKey
                  supers
                  ( odFromList $
                      odToList preArts ++ odToList clsArts ++ odToList postArts
                  )
                  clsExps
          !clsStageVar <- newTVar clsStage
          let !clsVal = EL'Value ms xsrc clsStageVar Nothing
          when (el'ctx'exporting eac) $
            iopdInsert clsKey clsVal exps
          el'Exit eas exit clsVal

      recvDataClassFields :: [ArgReceiver] -> STM EL'Artifacts
      recvDataClassFields !rcvrs = go [] rcvrs
        where
          entry :: AttrAddrSrc -> STM (EL'AttrKey, EL'Value)
          entry addr@(AttrAddrSrc _ !addr'span) = do
            !vstage <- newTVar EL'ParsedValue
            return
              ( el'AttrKey addr,
                EL'Value
                  ms
                  (ExprSrc (AttrExpr (DirectRef addr)) addr'span)
                  vstage
                  Nothing
              )
          go !entries [] = return $ odFromList $ reverse entries
          go !entries (rcvr : rest) = case rcvr of
            RecvArg addr@(AttrAddrSrc _ !addr'span) !asAttr _ -> do
              case asAttr of
                Nothing -> return ()
                Just {} ->
                  modifyTVar'
                    diags
                    ((addr'span, "renaming data class field") :)
              !e <- entry addr
              go (e : entries) rest
            RecvRestPosArgs !addr -> do
              !e <- entry addr
              go (e : entries) rest
            RecvRestKwArgs !addr -> do
              !e <- entry addr
              go (e : entries) rest
            RecvRestPkArgs !addr -> do
              !e <- entry addr
              go (e : entries) rest

el'LoadTopApk :: EL'TopLevels -> ArgsPacker -> EL'Analysis EL'ArgsPack
el'LoadTopApk !tops !argSenders !exit !eas = go [] [] argSenders
  where
    !eac = el'context eas
    !easApk =
      eas
        { el'context =
            eac
              { el'ctx'pure = True,
                el'ctx'exporting = False,
                el'ctx'eff'defining = False
              }
        }
    go ::
      [EL'Value] ->
      [(EL'AttrKey, EL'Value)] ->
      [ArgSender] ->
      STM ()
    go !loadedArgs !loadedKwArgs [] =
      el'Exit eas exit $
        EL'ArgsPack (reverse loadedArgs) (odFromList $ reverse loadedKwArgs)
    go !loadedArgs !loadedKwArgs (argSender : rest) = case argSender of
      SendPosArg !expr -> el'RunTx easApk $
        el'LoadTopExpr tops expr $
          \ !val _eas -> case val of
            -- todo special treatment?
            EL'Const {} -> go (val : loadedArgs) loadedKwArgs rest
            _ -> go (val : loadedArgs) loadedKwArgs rest
      SendKwArg !addr !expr -> el'RunTx easApk $
        el'LoadTopExpr tops expr $
          \ !val _eas -> case val of
            EL'Const {} ->
              -- todo special treatment?
              go loadedArgs ((el'AttrKey addr, val) : loadedKwArgs) rest
            _ -> go loadedArgs ((el'AttrKey addr, val) : loadedKwArgs) rest
      -- TODO handle args unpacking
      UnpackPosArgs _addr -> go loadedArgs loadedKwArgs rest
      UnpackKwArgs _addr -> go loadedArgs loadedKwArgs rest
      UnpackPkArgs _addr -> go loadedArgs loadedKwArgs rest

el'LoadClass ::
  EL'TopLevels ->
  StmtSrc ->
  EL'Analysis ([EL'Value], EL'Artifacts, EL'Artifacts)
el'LoadClass !tops !pbody !exit !eas = do
  !arts <- iopdEmpty
  !exts <- newTVar []
  !exps <- iopdEmpty
  el'RunTx
    eas
      { el'context =
          eac
            { el'ctx'pure = False,
              el'ctx'exporting = False,
              el'ctx'eff'defining = False
            }
      }
    $ el'LoadTopStmts
      tops
        { el'top'arts = arts,
          el'top'exts = exts,
          el'top'exps = exps
        }
      [pbody]
      $ \_ _eas -> do
        !arts' <- iopdSnapshot arts
        !exts' <- readTVar exts
        !exps' <- iopdSnapshot exps
        el'Exit eas exit (exts', arts', exps')
  where
    eac = el'context eas

el'DoResolveModule ::
  EL'ParsedModule ->
  TMVar EL'ResolvedModule ->
  EL'Analysis ()
el'DoResolveModule
  (EL'ParsedModule !stmts _parse'diags)
  !rmVar
  !exit
  !eas = do
    el'RunTx eas $
      el'AnalyzeStmts stmts $ \_ _eas -> do
        let !swip = el'ctx'scope eac
        !secs <- readTVar $ el'scope'secs'wip swip
        !region'end <- readTVar $ el'region'end'wip swip
        !region'annos <- iopdSnapshot $ el'region'annos'wip swip
        !region'attrs <- iopdSnapshot $ el'region'attrs'wip swip
        !region'effs <- iopdSnapshot $ el'region'effs'wip swip
        !diags <- readTVar $ el'scope'diags'wip swip
        let !fullRegion =
              EL'RegionSec $
                EL'Region
                  { el'region'span = SrcRange beginningSrcPos region'end,
                    el'region'annos = region'annos,
                    el'region'attrs = region'attrs,
                    el'region'effs = region'effs
                  }
        let !el'scope =
              EL'Scope
                { el'scope'span = SrcRange beginningSrcPos region'end,
                  el'scope'sections = V.fromList $! reverse $ fullRegion : secs
                }
            !resolved = EL'ResolvedModule el'scope $! reverse diags
        void $ tryPutTMVar rmVar resolved
        el'Exit eas exit ()
    where
      !eac = el'context eas

el'AnalyzeStmts :: [StmtSrc] -> EL'Analysis EL'Value
el'AnalyzeStmts !stmts !exit !eas = go stmts
  where
    go :: [StmtSrc] -> STM ()
    go [] = el'Exit eas exit $ EL'Const nil
    go (stmt : rest) = el'RunTx eas $
      el'AnalyzeStmt stmt $ \ !val _eas' -> case rest of
        [] -> el'Exit eas exit val
        _ -> go rest

el'AnalyzeStmt :: StmtSrc -> EL'Analysis EL'Value
el'AnalyzeStmt (StmtSrc !stmt !stmt'span) !exit !eas = case stmt of
  -- ExprStmt !expr _docCmt ->
  --   el'RunTx eas $
  --     el'AnalyzeExpr (ExprSrc expr stmt'span) exit
  -- LetStmt _argsRcvr _argsSndr -> do
  --   -- TODO recognize defines & exports
  --   el'Exit eas exit $ EL'Const nil
  ExtendsStmt _superExpr -> do
    case el'ctx'outers eac of
      [] -> modifyTVar' diags ((stmt'span, "extends from module") :)
      _ -> return ()
    el'Exit eas exit $ EL'Const nil
  -- TODO recognize more stmts
  -- EffectStmt !effs !docCmt -> undefined
  _ -> el'Exit eas exit $ EL'Const nil
  where
    !eac = el'context eas
    diags = el'scope'diags'wip $ el'ctx'scope eac
