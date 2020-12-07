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
    let !pars = el'modu'parsing ms
     in tryTakeTMVar pars >>= \case
          Nothing -> return ()
          Just parsing@EL'ModuParsing {} -> putTMVar pars parsing
          Just EL'ModuParsed {} -> return ()
  let !reso = el'modu'resolution ms
   in tryTakeTMVar reso >>= \case
        Nothing -> return ()
        Just resolving@EL'ModuResolving {} -> putTMVar reso resolving
        Just (EL'ModuResolved !resolved) ->
          let invalidateDependants ::
                [(EL'ModuSlot, Bool)] ->
                [(EL'ModuSlot, Bool)] ->
                STM ()
              invalidateDependants !upds [] = do
                unless (null upds) $
                  modifyTVar' (el'resolved'dependants resolved) $
                    -- todo maybe should delete instead of update here?
                    -- in case some module file is deleted, this'll leak?
                    Map.union (Map.fromList upds)
                exitEdh ets exit ()
              invalidateDependants !upds ((!dependant, !hold) : rest) =
                tryTakeTMVar (el'modu'resolution dependant) >>= \case
                  Nothing -> invalidateDependants upds rest
                  Just resolving@EL'ModuResolving {} -> do
                    putTMVar (el'modu'resolution dependant) resolving
                    invalidateDependants upds rest
                  Just (EL'ModuResolved !resolved') ->
                    Map.lookup ms {- HLINT ignore "Redundant <$>" -}
                      <$> readTVar (el'resolved'dependencies resolved')
                      >>= \case
                        Just True ->
                          runEdhTx ets $
                            el'InvalidateModule False dependant $ \_ _ets ->
                              invalidateDependants upds rest
                        _ ->
                          if hold
                            then
                              invalidateDependants
                                ((dependant, False) : upds)
                                rest
                            else invalidateDependants upds rest
           in readTVar (el'resolved'dependants resolved)
                >>= invalidateDependants [] . Map.toList

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
            !parsing <- newEmptyTMVar
            !resolution <- newEmptyTMVar
            -- !exports <- newEmptyTMVar
            -- !exps'upd <- newBroadcastTChan
            -- !dependants <- newTVar Map.empty
            -- !dependencies <- newTVar Map.empty
            let !ms =
                  EL'ModuSlot
                    home
                    relPath
                    (SrcDoc absFile)
                    parsing
                    resolution
            -- exports
            -- exps'upd
            -- dependants
            -- dependencies
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

el'LocateImportee :: EL'ModuSlot -> Text -> EL'Analysis (Either Text EL'ModuSlot)
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

asModuleParsed :: EL'ModuSlot -> (EL'ParsedModule -> EL'Tx) -> EL'Tx
asModuleParsed !ms !act' !eas =
  tryReadTMVar parsingVar >>= \case
    Nothing -> do
      !acts <- newTVar [\ !modu -> el'RunTx eas $ act' modu]
      -- the put will retry if parsingVar has been changed by others
      -- concurrently, so no duplicate effort would incur here
      putTMVar parsingVar (EL'ModuParsing acts)
      doParseModule $ \ !parsed -> do
        -- installed the parsed record
        tryTakeTMVar parsingVar >>= \case
          Just (EL'ModuParsing acts')
            | acts' == acts ->
              putTMVar parsingVar $ EL'ModuParsed parsed
          Just !other ->
            -- invalidated & new analysation wip
            putTMVar parsingVar other
          _ ->
            -- invalidated meanwhile
            return ()
        -- trigger post actions
        -- note they should just enque a proper Edh task to
        -- their respective initiating thread's task queue, so
        -- here we care neither about exceptions nor orders
        readTVar acts >>= sequence_ . (<*> pure parsed)
    Just (EL'ModuParsing !acts) -> modifyTVar' acts $
      -- always run the post action on the initiating thread
      -- TODO on entry, check not in an `ai` tx which this can break
      --
      -- note the action will appear executed out-of-order in this case, and
      -- further more, the action can cease execution if the initiating thread
      -- has terminated when the resolution done
      (:) $ \ !parsed -> el'RunTx eas $ act' parsed
    Just (EL'ModuParsed !parsed) -> el'RunTx eas $ act' parsed
  where
    !parsingVar = el'modu'parsing ms

    doParseModule :: (EL'ParsedModule -> STM ()) -> STM ()
    doParseModule !exit' = edhCatch
      (el'ets eas)
      doParse
      exit'
      $ \ !etsCatching !exv !recover !rethrow -> case exv of
        EdhNil -> rethrow nil
        _ -> edhValueDesc etsCatching exv $ \ !exDesc ->
          recover $
            EL'ParsedModule
              Nothing
              []
              [ el'Diag
                  el'Error
                  noSrcRange
                  "err-parse"
                  exDesc
              ]
      where
        doParse :: EdhTxExit EL'ParsedModule -> EdhTx
        doParse !exit !ets =
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
                  Right (!stmts, !docCmt) ->
                    exitEdh ets exit $ EL'ParsedModule docCmt stmts []
          where
            !world = edh'prog'world $ edh'thread'prog ets
            SrcDoc !moduFile = el'modu'doc ms

--
-- todo without an explicit CPS exit, the scheduled action would appear with
-- subsequent computations as of out-of-order-execution, this may work well
-- enough from the main loop of the LSP server, any possible gotchas ?
asModuleResolved :: EL'ModuSlot -> (EL'ResolvedModule -> EL'Tx) -> EL'Tx
asModuleResolved !ms !act' !eas =
  tryReadTMVar resoVar >>= \case
    Nothing -> do
      !acts <- newTVar [\ !modu -> el'RunTx eas $ act' modu]
      -- the put will retry if parsingVar has been changed by others
      -- concurrently, so no duplicate effort would incur here
      putTMVar resoVar (EL'ModuResolving acts)
      doResolveModule $ \ !resolved -> do
        -- installed the resolved record
        tryTakeTMVar resoVar >>= \case
          Just (EL'ModuResolving acts')
            | acts' == acts ->
              putTMVar resoVar $ EL'ModuResolved resolved
          Just !other ->
            -- invalidated & new analysation wip
            putTMVar resoVar other
          _ ->
            -- invalidated meanwhile
            return ()
        -- trigger post actions
        -- note they should just enque a proper Edh task to
        -- their respective initiating thread's task queue, so
        -- here we care neither about exceptions nor orders
        readTVar acts >>= sequence_ . (<*> pure resolved)
    Just (EL'ModuResolving !acts) -> modifyTVar' acts $
      -- always run the post action on the initiating thread
      -- TODO on entry, check not in an `ai` tx which this can break
      --
      -- note the action will appear executed out-of-order in this case, and
      -- further more, the action can cease execution if the initiating thread
      -- has terminated when the parsing done
      (:) $ \ !resolved -> el'RunTx eas $ act' resolved
    Just (EL'ModuResolved !resolved) -> el'RunTx eas $ act' resolved
  where
    !eac = el'context eas
    !resoVar = el'modu'resolution ms

    doResolveModule :: (EL'ResolvedModule -> STM ()) -> STM ()
    doResolveModule !exit' = el'RunTx eas $
      asModuleParsed ms $ \ !parsed _eas -> edhCatch
        (el'ets eas)
        (doResolve $ el'modu'stmts parsed)
        exit'
        $ \ !etsCatching !exv !recover !rethrow -> case exv of
          EdhNil -> rethrow nil
          _ -> edhValueDesc etsCatching exv $ \ !exDesc -> do
            !expsVar <- iopdEmpty
            !dependantsVar <- newTVar Map.empty
            !dependenciesVar <- newTVar Map.empty
            recover $
              EL'ResolvedModule
                ( EL'Scope
                    noSrcRange
                    V.empty
                    odEmpty
                    odEmpty
                    V.empty
                )
                expsVar
                dependantsVar
                dependenciesVar
                [ el'Diag
                    el'Error
                    noSrcRange
                    "resolve-err"
                    exDesc
                ]

    doResolve :: [StmtSrc] -> EdhTxExit EL'ResolvedModule -> EdhTx
    doResolve !stmts !exit !ets = do
      !diagsVar <- newTVar []
      !moduExts <- newTVar []
      !moduExps <- iopdEmpty
      !moduDependants <- newTVar Map.empty
      !moduDepencencies <- newTVar Map.empty
      !moduAttrs <- iopdEmpty
      !moduEffs <- iopdEmpty
      !moduAnnos <- iopdEmpty
      !endPos <- newTVar beginningSrcPos
      !moduSecs <- newTVar []
      !moduSyms <- newTVar []
      let !pwip =
            EL'RunProc
              moduExts
              moduExps
              moduAttrs
              moduEffs
              moduAnnos
              endPos
              moduSecs
              moduSyms

          !eacModu =
            eac
              { el'ctx'diags = diagsVar,
                el'ctx'scope =
                  EL'ModuWIP
                    ms
                    ( EL'InitModu
                        moduExts
                        moduExps
                        moduDependants
                        moduDepencencies
                    )
                    pwip,
                el'ctx'outers = el'ctx'scope eac : el'ctx'outers eac
              }
          !easModu = eas {el'context = eacModu}

      el'RunTx easModu $
        el'AnalyzeStmts stmts $ \_ _eas -> do
          !diags <- readTVar diagsVar
          !scope'attrs <- iopdSnapshot moduAttrs
          !scope'effs <- iopdSnapshot moduEffs
          !scope'end <- readTVar endPos
          !secs <- readTVar moduSecs
          !scope'symbols <- readTVar moduSyms
          let !fullRegion =
                EL'RegionSec $
                  EL'Region
                    { el'region'span = SrcRange beginningSrcPos scope'end,
                      el'region'attrs = scope'attrs
                    }
          let !el'scope =
                EL'Scope
                  { el'scope'span = SrcRange beginningSrcPos scope'end,
                    el'scope'sections =
                      V.fromList $! reverse $ fullRegion : secs,
                    el'scope'attrs = scope'attrs,
                    el'scope'effs = scope'effs,
                    el'scope'symbols = V.fromList $! reverse scope'symbols
                  }
          exitEdh ets exit $
            EL'ResolvedModule
              el'scope
              moduExps
              moduDependants
              moduDepencencies
              (reverse diags)

el'AnalyzeStmts :: [StmtSrc] -> EL'Analysis EL'Value
el'AnalyzeStmts !stmts !exit !eas = go stmts
  where
    go :: [StmtSrc] -> STM ()
    go [] = el'Exit eas exit $ EL'Const nil
    go (stmt : rest) = el'RunTx eas $
      el'AnalyzeStmt stmt $ \ !val _eas' -> case rest of
        [] -> el'Exit eas exit val
        _ -> go rest

-- | analyze a statement in context
el'AnalyzeStmt :: StmtSrc -> EL'Analysis EL'Value
--

-- a standalone expression
el'AnalyzeStmt (StmtSrc (ExprStmt !expr !docCmt) !stmt'span) !exit !eas =
  el'RunTx eas $ el'AnalyzeExpr docCmt (ExprSrc expr stmt'span) exit
--

el'AnalyzeStmt (StmtSrc (LetStmt _argsRcvr _argsSndr) _stmt'span) !exit !eas =
  -- TODO recognize defines & exports
  el'Exit eas exit $ EL'Const nil
--

-- effect defining
el'AnalyzeStmt (StmtSrc (EffectStmt !effs !docCmt) _stmt'span) !exit !eas =
  el'RunTx eas {el'context = eac {el'ctx'eff'defining = True}} $
    el'AnalyzeExpr docCmt effs $ \_ -> el'ExitTx exit $ EL'Const nil
  where
    !eac = el'context eas
--

-- extending
el'AnalyzeStmt (StmtSrc (ExtendsStmt !superExpr) !stmt'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing superExpr $ \case
      EL'ObjVal !superObj -> \_eas -> do
        modifyTVar' (el'scope'exts'wip pwip) (++ [superObj])
        el'Exit eas exit $ EL'Const nil
      EL'Apk (EL'ArgsPack !superVals !kwargs) | odNull kwargs -> \_eas -> do
        !superObjs <- (catMaybes <$>) $
          sequence $
            flip fmap superVals $ \case
              EL'ObjVal !superObj -> return $ Just superObj
              !badSuperVal -> do
                el'LogDiag
                  diags
                  el'Warning
                  stmt'span
                  "invalid-extends"
                  $ "not an object to extend: " <> T.pack (show badSuperVal)
                return Nothing
        modifyTVar' (el'scope'exts'wip pwip) (++ superObjs)
        el'Exit eas exit $ EL'Const nil
      !badSuperVal -> \_eas -> do
        el'LogDiag
          diags
          el'Warning
          stmt'span
          "invalid-extends"
          $ "not an object to extend: " <> T.pack (show badSuperVal)
        el'Exit eas exit $ EL'Const nil
  where
    !eac = el'context eas
    diags = el'ctx'diags eac

    scope = el'ctx'scope eac
    pwip = el'ProcWIP scope
--

-- TODO recognize more stmts

-- the rest of statements not analyzed
el'AnalyzeStmt _stmt !exit !eas =
  el'Exit eas exit $ EL'Const nil

--

-- | analyze an expression in context
el'AnalyzeExpr :: Maybe DocComment -> ExprSrc -> EL'Analysis EL'Value
--

-- call making
el'AnalyzeExpr
  _docCmt
  xsrc@(ExprSrc (CallExpr !calleeExpr !argsSndr) _expr'span)
  !exit
  !eas =
    case calleeExpr of
      ExprSrc (AttrExpr (DirectRef (AttrAddrSrc (NamedAttr "Symbol") _))) _ ->
        case argsSndr of
          [SendPosArg (ExprSrc (LitExpr (StringLiteral !symRepr)) _)] ->
            mkSymbol symRepr >>= el'Exit eas exit . EL'Const . EdhSymbol
          _ -> do
            el'LogDiag
              diags
              el'Error
              (exprSrcSpan calleeExpr)
              "invalid-symbol"
              "invalid argument to create a Symbol"
            el'Exit eas exit $ EL'Const nil
      _ ->
        -- TODO analyze other calls
        returnAsExpr
    where
      {- HLINT ignore "Reduce duplication" -}
      !eac = el'context eas
      diags = el'ctx'diags eac
      returnAsExpr = el'Exit eas exit $ EL'Expr xsrc
--

-- exporting
el'AnalyzeExpr !docCmt (ExprSrc (ExportExpr !expr') _expr'span) !exit !eas =
  el'RunTx eas {el'context = eac {el'ctx'exporting = True}} $
    el'AnalyzeExpr docCmt expr' exit
  where
    !eac = el'context eas
--

-- importing
el'AnalyzeExpr
  !docCmt
  xsrc@( ExprSrc
           ( ImportExpr
               !argsRcvr
               impSpec@(ExprSrc !specExpr !spec'span)
               !maybeInto
             )
           !expr'span
         )
  !exit
  !eas =
    case maybeInto of
      Just _intoExpr ->
        returnAsExpr -- TODO handle importing into some object
      Nothing -> case specExpr of
        LitExpr (StringLiteral !litSpec) -> case el'ContextModule eac of
          Nothing -> do
            el'LogDiag
              diags
              el'Error
              spec'span
              "moduleless-import"
              "import from non-module context"
            el'Exit eas exit $ EL'Const nil
          Just (!msImporter, _miImporter) -> el'RunTx eas $
            el'LocateImportee msImporter litSpec $ \ !impResult _eas ->
              case impResult of
                Left !err -> do
                  el'LogDiag diags el'Error spec'span "err-import" err
                  el'Exit eas exit $ EL'Const nil
                Right !msImportee -> do
                  !chkExp <- chkExport
                  el'RunTx eas $
                    asModuleResolved msImportee $ \ !resolved _eas ->
                      -- TODO find mechanism in LSP to report diags discovered
                      -- here asynchronously, to not missing them
                      impIntoScope
                        chkExp
                        msImportee
                        resolved
                        argsRcvr
                  -- above can finish synchronously or asynchronously, return
                  -- the importee module now anyway, as waiting for the
                  -- resolved record is deadlock prone here, in case of cyclic
                  -- imports
                  el'Exit eas exit $ EL'ModuVal msImportee
        AttrExpr {} ->
          el'RunTx eas $ -- obj import
            el'AnalyzeExpr Nothing impSpec $ \ !impFromVal -> do
              -- TODO validate it is object type, import from it
              el'ExitTx exit impFromVal
        _ -> do
          el'LogDiag
            diags
            el'Warning
            spec'span
            "dynamic-import"
            "dynamic import specification not analyzed yet"
          el'Exit eas exit $ EL'Const nil
    where
      !eac = el'context eas
      diags = el'ctx'diags eac
      returnAsExpr = el'Exit eas exit $ EL'Expr xsrc

      currScope = el'ctx'scope eac
      pwip = el'ProcWIP currScope

      chkExport :: STM (AttrKey -> EL'AttrDef -> STM ())
      chkExport =
        if not (el'ctx'exporting eac)
          then return $ \_ _ -> return ()
          else
            let !localExps = el'scope'exps'wip pwip
             in return $ \ !localKey !attrDef ->
                  iopdInsert localKey attrDef localExps

      impIntoScope ::
        (AttrKey -> EL'AttrDef -> STM ()) ->
        EL'ModuSlot ->
        EL'ResolvedModule ->
        ArgsReceiver ->
        STM ()
      impIntoScope !chkExp !srcModu !srcResolved !asr = do
        case el'ContextModule eac of
          Nothing -> pure ()
          Just (!localModu, !localInit) -> do
            modifyTVar' (el'resolved'dependants srcResolved) $
              Map.insert localModu True
            modifyTVar' (el'modu'dependencies localInit) $
              Map.insert srcModu True
        odMap (EL'External srcModu)
          <$> iopdSnapshot
            (el'resolved'exports srcResolved)
            >>= \ !srcArts -> case asr of
              WildReceiver -> sequence_ $ wildImp <$> odToList srcArts
              PackReceiver !ars -> go srcArts ars
              SingleReceiver !ar -> go srcArts [ar]
        where
          !localTgt =
            if el'ctx'eff'defining eac
              then el'scope'effs'wip pwip
              else el'scope'attrs'wip pwip

          wildImp :: (AttrKey, EL'Value) -> STM ()
          wildImp (!k, !v) = do
            !artAnno <- newTVar =<< el'ResolveAnnotation currScope k
            let !attrDef =
                  EL'AttrDef
                    k
                    docCmt
                    "<import>"
                    expr'span
                    xsrc
                    v
                    artAnno
                    Nothing

            iopdInsert k attrDef localTgt
            chkExp k attrDef

          go :: OrderedDict AttrKey EL'Value -> [ArgReceiver] -> STM ()
          go !srcArts [] =
            if odNull srcArts
              then return () -- very well expected
              else
                el'LogDiag
                  diags
                  el'Error
                  spec'span
                  "non-exhaustive-import"
                  $ "import is not exhaustive, "
                    <> if odSize srcArts <= 8
                      then
                        "also exported: "
                          <> T.intercalate
                            ", "
                            (attrKeyStr <$> odKeys srcArts)
                      else T.pack (show $ odSize srcArts) <> " more exported"
          go !srcArts (ar : rest) = case ar of
            RecvArg srcAddr@(AttrAddrSrc _ !item'span) !maybeAs !defExpr -> do
              case defExpr of
                Nothing -> pure ()
                Just {} ->
                  el'LogDiag
                    diags
                    el'Warning
                    item'span
                    "unusual-import"
                    "defaults in import specificatin is not analyzed yet"
              case maybeAs of
                Nothing -> processImp srcAddr srcAddr
                Just (DirectRef !asAddr) -> processImp srcAddr asAddr
                Just !badRename ->
                  el'LogDiag
                    diags
                    el'Error
                    item'span
                    "invalid-import-rename"
                    $ "invalid rename of import: " <> T.pack (show badRename)
            RecvRestPosArgs (AttrAddrSrc _ bad'span) ->
              el'LogDiag
                diags
                el'Error
                bad'span
                "rest-pos-import"
                "rest positional receiver in import specification"
            RecvRestPkArgs (AttrAddrSrc _ bad'span) ->
              el'LogDiag
                diags
                el'Error
                bad'span
                "rest-apk-import"
                "rest apk receiver in import specification"
            RecvRestKwArgs localAddr@(AttrAddrSrc _ !addr'span) ->
              el'ResolveAttrAddr eac localAddr >>= \case
                Nothing ->
                  -- invalid attr addr, error should have been logged
                  go srcArts rest
                Just (AttrByName "_") -> go odEmpty rest -- explicit dropping
                Just !localKey -> do
                  !artAnno <-
                    newTVar
                      =<< el'ResolveAnnotation
                        currScope
                        localKey
                  let !kwVal = EL'Apk $ EL'ArgsPack [] srcArts
                      !attrDef =
                        EL'AttrDef
                          localKey
                          docCmt
                          "<import>"
                          addr'span
                          xsrc
                          kwVal
                          artAnno
                          Nothing

                  iopdInsert localKey attrDef localTgt
                  chkExp localKey attrDef

                  go odEmpty rest
            where
              processImp :: AttrAddrSrc -> AttrAddrSrc -> STM ()
              processImp srcAddr@(AttrAddrSrc _ !src'span) !localAddr = do
                el'ResolveAttrAddr eac localAddr >>= \case
                  Nothing ->
                    -- invalid attr addr, error should have been logged
                    go srcArts rest
                  Just !localKey ->
                    el'ResolveAttrAddr eac srcAddr >>= \case
                      Nothing ->
                        -- invalid attr addr, error should have been logged
                        go srcArts rest
                      Just !srcKey ->
                        let (!gotArt, !srcArts') = odTakeOut srcKey srcArts
                         in case gotArt of
                              Nothing -> do
                                el'LogDiag
                                  diags
                                  el'Error
                                  src'span
                                  "missing-import"
                                  $ "no such artifact to import: "
                                    <> attrKeyStr srcKey
                                go srcArts' rest
                              Just !srcVal -> do
                                !artAnno <-
                                  newTVar
                                    =<< el'ResolveAnnotation
                                      currScope
                                      localKey
                                let !attrDef =
                                      EL'AttrDef
                                        localKey
                                        docCmt
                                        "<import>"
                                        src'span
                                        xsrc
                                        srcVal
                                        artAnno
                                        Nothing

                                iopdInsert localKey attrDef localTgt
                                chkExp localKey attrDef

                                go srcArts' rest
--

-- defining a class
el'AnalyzeExpr _ (ExprSrc (ClassExpr HostDecl {}) _expr'span) _exit _eas =
  error "bug: host class decl"
el'AnalyzeExpr
  !docCmt
  xsrc@( ExprSrc
           ( ClassExpr
               ( ProcDecl
                   cls'name@(AttrAddrSrc _cls'name'addr !cls'name'span)
                   !argsRcvr
                   cls'body@(StmtSrc _body'stmt !body'span)
                   _cls'proc'loc
                 )
             )
           _expr'span
         )
  !exit
  !eas =
    el'ResolveAttrAddr eac cls'name >>= \case
      Nothing -> el'Exit eas exit $ EL'Const nil
      Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
      Just !clsName -> do
        let SrcRange !beginPos !endPos = body'span
        !clsExts <- newTVar []
        !instExts <- newTVar []
        !clsExps <- iopdEmpty
        !instExps <- iopdEmpty
        !clsAttrs <- iopdEmpty
        !clsEffs <- iopdEmpty
        !clsAnnos <- iopdEmpty
        !scopeEnd <- newTVar beginPos
        !clsSecs <- newTVar []
        !clsSyms <- newTVar []
        let !pwip =
              EL'RunProc
                clsExts
                clsExps
                clsAttrs
                clsEffs
                clsAnnos
                scopeEnd
                clsSecs
                clsSyms
            !eacCls =
              eac
                { el'ctx'scope =
                    EL'ClassWIP
                      ( EL'DefineClass
                          clsExts
                          instExts
                          clsExps
                          instExps
                      )
                      pwip,
                  el'ctx'outers = outerScope : el'ctx'outers eac
                }
            !easCls = eas {el'context = eacCls}

            -- define artifacts from arguments (i.e. data fields) for a data
            -- class
            defDataArts :: [ArgReceiver] -> STM ()
            defDataArts !ars = flip iopdUpdate clsAttrs =<< go [] ars
              where
                go ::
                  [(AttrKey, EL'AttrDef)] ->
                  [ArgReceiver] ->
                  STM [(AttrKey, EL'AttrDef)]
                go !dfs [] = return $ reverse dfs
                go !dfs (ar : rest) = case ar of
                  RecvArg
                    dfAddr@(AttrAddrSrc _ df'span)
                    !maybeRename
                    _maybeDef ->
                      case maybeRename of
                        Nothing -> defDataField dfAddr
                        Just (DirectRef !dfAddr') -> defDataField dfAddr'
                        Just _badRename -> do
                          el'LogDiag
                            diags
                            el'Error
                            df'span
                            "bad-data-field-rename"
                            "bad data field rename"
                          go dfs rest
                  RecvRestPkArgs !dfAddr -> defDataField dfAddr
                  RecvRestKwArgs !dfAddr -> defDataField dfAddr
                  RecvRestPosArgs !dfAddr -> defDataField dfAddr
                  where
                    defDataField dfAddr@(AttrAddrSrc _ df'name'span) =
                      el'ResolveAttrAddr eac dfAddr >>= \case
                        Nothing -> go dfs rest
                        Just !dfKey -> do
                          !dfAnno <- newTVar =<< iopdLookup dfKey clsAnnos
                          go
                            ( ( dfKey,
                                EL'AttrDef
                                  dfKey
                                  Nothing
                                  "<data-class-field>"
                                  df'name'span
                                  xsrc
                                  ( EL'Expr
                                      ( ExprSrc
                                          (AttrExpr (DirectRef dfAddr))
                                          df'name'span
                                      )
                                  )
                                  dfAnno
                                  Nothing
                              ) :
                              dfs
                            )
                            rest

        -- define intrinsic methods of the data class
        (flip iopdUpdate clsAttrs =<<) $
          forM
            [ ("__repr__", "data class repr"),
              ("__str__", "data class str"),
              ("__eq__", "data class eq test"),
              ("__compare__", "data class comparision")
            ]
            $ \(!mthName, !mthDoc) -> do
              !anno <- newTVar Nothing
              return -- todo synthesize their respective anno ?
                ( AttrByName mthName,
                  EL'AttrDef
                    (AttrByName mthName)
                    (Just [mthDoc])
                    "<data-class-def>"
                    cls'name'span
                    xsrc
                    ( EL'ProcVal
                        ( EL'Proc
                            (AttrByName mthName)
                            ( EL'Scope
                                cls'name'span
                                V.empty
                                odEmpty
                                odEmpty
                                V.empty
                            )
                        )
                    )
                    anno
                    Nothing
                )

        el'RunTx easCls $
          el'AnalyzeStmts [cls'body] $ \_ _eas -> do
            case argsRcvr of
              -- a normal class
              WildReceiver -> pure ()
              -- a data class (ADT)
              SingleReceiver !ar -> defDataArts [ar]
              PackReceiver !ars -> defDataArts ars
            !cls'exts <- readTVar clsExts
            !scope'attrs <- iopdSnapshot clsAttrs
            !scope'effs <- iopdSnapshot clsEffs
            !secs <- readTVar clsSecs
            !scope'symbols <- readTVar clsSyms
            !clsAnno <- newTVar =<< el'ResolveAnnotation outerScope clsName
            let !fullRegion =
                  EL'RegionSec $
                    EL'Region
                      { el'region'span = body'span,
                        el'region'attrs = scope'attrs
                      }
            let !cls'scope =
                  EL'Scope
                    { el'scope'span = body'span,
                      el'scope'sections =
                        V.fromList $! reverse $ fullRegion : secs,
                      el'scope'attrs = scope'attrs,
                      el'scope'effs = scope'effs,
                      el'scope'symbols = V.fromList $! reverse scope'symbols
                    }
                !mro = [] -- TODO C3 linearize cls'exts to get this
                !cls = EL'Class clsName cls'exts mro cls'scope clsExps
                !clsVal = EL'ClsVal cls
                !clsDef =
                  EL'AttrDef
                    clsName
                    docCmt
                    "<class-def>"
                    cls'name'span
                    xsrc
                    clsVal
                    clsAnno
                    Nothing
            --

            -- record as artifact of outer scope
            unless (el'ctx'pure eac) $ do
              iopdInsert clsName clsDef $
                if el'ctx'eff'defining eac
                  then el'scope'effs'wip outerProc
                  else el'scope'attrs'wip outerProc
              when (el'ctx'exporting eac) $
                iopdInsert clsName clsDef $ el'scope'exps'wip outerProc
            -- record as definition symbol of outer scope
            modifyTVar' (el'scope'symbols'wip outerProc) (EL'DefSym clsDef :)

            -- append the scope as a section to outer scope
            modifyTVar' (el'scope'secs'wip outerProc) (EL'ScopeSec cls'scope :)
            -- extend outer scope end pos
            writeTVar (el'scope'end'wip outerProc) endPos

            -- return the class object value
            el'Exit eas exit clsVal
    where
      !eac = el'context eas
      !outerScope = el'ctx'scope eac
      !outerProc = el'ProcWIP outerScope
      diags = el'ctx'diags eac
--

-- defining a method
el'AnalyzeExpr _ (ExprSrc (MethodExpr HostDecl {}) _expr'span) _exit _eas =
  error "bug: host method decl"
el'AnalyzeExpr
  !docCmt
  xsrc@( ExprSrc
           ( MethodExpr
               ( ProcDecl
                   mth'name@(AttrAddrSrc _mth'name'addr !mth'name'span)
                   !argsRcvr
                   mth'body@(StmtSrc _body'stmt !body'span)
                   _mth'proc'loc
                 )
             )
           _expr'span
         )
  !exit
  !eas =
    el'ResolveAttrAddr eac mth'name >>= \case
      Nothing -> el'Exit eas exit $ EL'Const nil
      Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
      Just !mthName -> do
        let SrcRange !beginPos !endPos = body'span
        !mthAttrs <- iopdEmpty
        !mthEffs <- iopdEmpty
        !mthAnnos <- iopdEmpty
        !scopeEnd <- newTVar beginPos
        !mthSecs <- newTVar []
        !mthSyms <- newTVar []
        let !pwip =
              outerProc -- inherit exts/exps from outer scope
                { el'scope'attrs'wip = mthAttrs,
                  el'scope'effs'wip = mthEffs,
                  el'scope'annos'wip = mthAnnos,
                  el'scope'end'wip = scopeEnd,
                  el'scope'secs'wip = mthSecs,
                  el'scope'symbols'wip = mthSyms
                }
            !eacMth =
              eac
                { el'ctx'scope = EL'ProcWIP pwip,
                  el'ctx'outers = outerScope : el'ctx'outers eac
                }
            !easMth = eas {el'context = eacMth}

        !argArts <- case argsRcvr of
          WildReceiver -> return []
          PackReceiver !ars -> defArgArts ars
          SingleReceiver !ar -> defArgArts [ar]
        iopdUpdate argArts mthAttrs

        el'RunTx easMth $
          el'AnalyzeStmts [mth'body] $ \_ _eas -> do
            -- update annotations for arguments from body
            forM_ argArts $ \(!argName, !argDef) ->
              iopdLookup argName mthAnnos >>= \case
                Nothing -> pure ()
                Just !anno -> writeTVar (el'attr'def'anno argDef) $ Just anno
            --
            !scope'attrs <- iopdSnapshot mthAttrs
            !scope'effs <- iopdSnapshot mthEffs
            !secs <- readTVar mthSecs
            !scope'symbols <- readTVar mthSyms
            !mthAnno <- newTVar =<< el'ResolveAnnotation outerScope mthName
            let !fullRegion =
                  EL'RegionSec $
                    EL'Region
                      { el'region'span = body'span,
                        el'region'attrs = scope'attrs
                      }
            let !mth'scope =
                  EL'Scope
                    { el'scope'span = body'span,
                      el'scope'sections =
                        V.fromList $! reverse $ fullRegion : secs,
                      el'scope'attrs = scope'attrs,
                      el'scope'effs = scope'effs,
                      el'scope'symbols = V.fromList $! reverse scope'symbols
                    }
                !mth = EL'Proc mthName mth'scope
                !mthVal = EL'ProcVal mth
                !mthDef =
                  EL'AttrDef
                    mthName
                    docCmt
                    "<method-def>"
                    mth'name'span
                    xsrc
                    mthVal
                    mthAnno
                    Nothing
            --

            -- record as artifact of outer scope
            unless (el'ctx'pure eac) $ do
              iopdInsert mthName mthDef $
                if el'ctx'eff'defining eac
                  then el'scope'effs'wip outerProc
                  else el'scope'attrs'wip outerProc
              when (el'ctx'exporting eac) $
                iopdInsert mthName mthDef $ el'scope'exps'wip outerProc
            -- record as definition symbol of outer scope
            modifyTVar' (el'scope'symbols'wip outerProc) (EL'DefSym mthDef :)

            -- append the scope as a section to outer scope
            modifyTVar' (el'scope'secs'wip outerProc) (EL'ScopeSec mth'scope :)
            -- extend outer scope end pos
            writeTVar (el'scope'end'wip outerProc) endPos

            -- return the procedure object value
            el'Exit eas exit mthVal
    where
      !eac = el'context eas
      !outerScope = el'ctx'scope eac
      !outerProc = el'ProcWIP outerScope
      -- diags = el'ctx'diags eac

      -- define artifacts from arguments for a procedure
      defArgArts :: [ArgReceiver] -> STM [(AttrKey, EL'AttrDef)]
      defArgArts !ars = go [] ars
        where
          go ::
            [(AttrKey, EL'AttrDef)] ->
            [ArgReceiver] ->
            STM [(AttrKey, EL'AttrDef)]
          go !args [] = return $ reverse args
          go !args (ar : rest) = case ar of
            RecvArg !argAddr !maybeRename !maybeDef -> case maybeRename of
              Nothing -> defArgArt argAddr maybeDef
              Just (DirectRef !argAddr') -> defArgArt argAddr' Nothing
              Just _otherRename -> go args rest -- TODO elaborate?
            RecvRestPkArgs !argAddr -> defArgArt argAddr Nothing
            RecvRestKwArgs !argAddr -> defArgArt argAddr Nothing
            RecvRestPosArgs !argAddr -> defArgArt argAddr Nothing
            where
              defArgArt argAddr@(AttrAddrSrc _ arg'name'span) !knownExpr =
                el'ResolveAttrAddr eac argAddr >>= \case
                  Nothing -> go args rest
                  Just !argKey ->
                    newTVar Nothing >>= \ !anno ->
                      go
                        ( ( argKey,
                            EL'AttrDef
                              argKey
                              Nothing
                              "<procedure-argument>"
                              arg'name'span
                              xsrc
                              ( EL'Expr $
                                  fromMaybe
                                    ( ExprSrc
                                        (AttrExpr (DirectRef argAddr))
                                        arg'name'span
                                    )
                                    knownExpr
                              )
                              anno
                              Nothing
                          ) :
                          args
                        )
                        rest

--

-- apk ctor
el'AnalyzeExpr _ (ExprSrc (ArgsPackExpr !argSndrs) _expr'span) !exit !eas =
  undefined
--

-- TODO recognize more exprs

-- the rest of expressions not analyzed
el'AnalyzeExpr _docCmt !xsrc !exit !eas =
  el'Exit eas exit $ EL'Expr xsrc
