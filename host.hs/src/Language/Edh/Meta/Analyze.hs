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
  when srcChanged $
    void $ tryTakeTMVar $ el'modu'parsed ms
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
                                      ( EL'Scope
                                          noSrcRange
                                          V.empty
                                          odEmpty
                                          odEmpty
                                          V.empty
                                      )
                                      [ el'Diag
                                          el'Error
                                          noSrcRange
                                          "no-resolve"
                                          "module not resolved"
                                      ]
                                runEdhTx etsCatching $ rethrow nil
                              !exv -> edhValueDesc etsCatching exv $
                                \ !exDesc -> do
                                  void $ -- in case it's not filled
                                    tryPutTMVar rmVar $
                                      EL'ResolvedModule
                                        ( EL'Scope
                                            noSrcRange
                                            V.empty
                                            odEmpty
                                            odEmpty
                                            V.empty
                                        )
                                        [ el'Diag
                                            el'Error
                                            noSrcRange
                                            "err-resolve"
                                            exDesc
                                        ]
                                  runEdhTx etsCatching $ recover nil
                      )
                      endOfEdh
                  el'Exit eas exit rmVar
    goResolve
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
                                  [ el'Diag
                                      el'Error
                                      noSrcRange
                                      "no-parse"
                                      "module not parsed"
                                  ]
                            runEdhTx etsCatching $ rethrow nil
                          !exv -> edhValueDesc etsCatching exv $ \ !exDesc -> do
                            void $ -- in case it's not filled
                              tryPutTMVar pmVar $
                                EL'ParsedModule
                                  []
                                  [ el'Diag
                                      el'Error
                                      noSrcRange
                                      "err-parse"
                                      exDesc
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
                >>= atomically
                  . goWith
                    scriptName
                    relPath
                    absFile
                    el'home'scripts
            Right (Right (!homePath, !moduName, !relPath, !absFile)) ->
              atomically (prepareHome homePath)
                -- with 2 separate STM txs
                >>= atomically
                  . goWith
                    moduName
                    relPath
                    absFile
                    el'home'modules
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

el'DoResolveModule ::
  EL'ParsedModule ->
  TMVar EL'ResolvedModule ->
  EL'Analysis ()
el'DoResolveModule
  (EL'ParsedModule !stmts _parse'diags)
  !rmVar
  !exit
  !eas = do
    !diagsVar <- newTVar []
    let !eac = (el'context eas) {el'ctx'diags = diagsVar}
        !easModu = eas {el'context = eac}
    el'RunTx easModu $
      el'AnalyzeStmts stmts $ \_ _eas -> do
        !diags <- readTVar diagsVar
        let !swip = el'wip'proc $ el'ctx'scope eac
        !scope'attrs <- iopdSnapshot $ el'scope'attrs'wip swip
        !scope'effs <- iopdSnapshot $ el'scope'effs'wip swip
        !scope'end <- readTVar $ el'scope'end'wip swip
        !secs <- readTVar $ el'scope'secs'wip swip
        !scope'symbols <- readTVar $ el'scope'symbols'wip swip
        let !fullRegion =
              EL'RegionSec $
                EL'Region
                  { el'region'span = SrcRange beginningSrcPos scope'end,
                    el'region'attrs = scope'attrs
                  }
        let !el'scope =
              EL'Scope
                { el'scope'span = SrcRange beginningSrcPos scope'end,
                  el'scope'sections = V.fromList $! reverse $ fullRegion : secs,
                  el'scope'attrs = scope'attrs,
                  el'scope'effs = scope'effs,
                  el'scope'symbols = V.fromList $! reverse scope'symbols
                }
            !resolved = EL'ResolvedModule el'scope $! reverse diags
        void $ tryPutTMVar rmVar resolved
        el'Exit eas exit ()

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
  ExprStmt !expr _docCmt ->
    el'RunTx eas $
      el'AnalyzeExpr (ExprSrc expr stmt'span) exit
  -- LetStmt _argsRcvr _argsSndr -> do
  --   -- TODO recognize defines & exports
  --   el'Exit eas exit $ EL'Const nil
  ExtendsStmt _superExpr -> do
    case el'ctx'outers eac of
      [] ->
        el'LogDiag
          diags
          el'Warning
          stmt'span
          "extends from module"
          "Maybe not a good idea to have super objects for a module"
      _ -> return ()
    el'Exit eas exit $ EL'Const nil
  EffectStmt !effs _docCmt ->
    el'RunTx eas {el'context = eac {el'ctx'eff'defining = True}} $
      el'AnalyzeExpr effs $ \_ -> el'ExitTx exit $ EL'Const nil
  --

  -- TODO recognize more stmts
  _ -> el'Exit eas exit $ EL'Const nil
  where
    !eac = el'context eas
    diags = el'ctx'diags eac

el'AnalyzeExpr :: ExprSrc -> EL'Analysis EL'Value
el'AnalyzeExpr xsrc@(ExprSrc !expr _expr'span) !exit !eas = case expr of
  ExportExpr !expr' ->
    el'RunTx eas {el'context = eac {el'ctx'exporting = True}} $
      el'AnalyzeExpr expr' exit
  --

  -- importing
  ImportExpr !argsRcvr impSpec@(ExprSrc !specExpr spec'span) !maybeInto ->
    case maybeInto of
      Just !intoExpr ->
        rtnParsed -- TODO handle re-targeted import
      Nothing -> case specExpr of
        LitExpr (StringLiteral !litSpec) -> el'RunTx eas $
          el'LocateImportee litSpec $ \ !impResult _eas -> case impResult of
            Left !err -> do
              el'LogDiag diags el'Error spec'span "err-import" err
              el'Exit eas exit $ EL'Const nil
            Right !msFrom -> el'RunTx
              eas
                { el'context = eac {el'ctx'module = msFrom}
                }
              $ el'ResolveModule $ \_resolvedImportee _eas ->
                tryReadTMVar (el'modu'exports msFrom) >>= \case
                  Just !expsFrom ->
                    undefined -- TODO importee already resolved
                  Nothing ->
                    undefined -- TODO importee not resolved yet
        AttrExpr {} ->
          el'RunTx eas $ -- obj import
            el'AnalyzeExpr impSpec $ \ !impFromVal -> do
              -- TODO validate it is object type, import from it
              el'ExitTx exit impFromVal
        _ -> do
          el'LogDiag
            diags
            el'Error
            spec'span
            "bad-import"
            "invalid import specification"
          el'Exit eas exit $ EL'Const nil
  --

  -- TODO recognize more exprs
  -- CaseExpr !tgtExpr !branchesExpr -> undefined
  -- ForExpr !argsRcvr !iterExpr !doStmt -> undefined
  -- CallExpr !calleeExpr !argsSndr -> undefined
  _ -> rtnParsed
  where
    !eac = el'context eas
    diags = el'ctx'diags eac
    rtnParsed = el'Exit eas exit $ EL'Expr xsrc
