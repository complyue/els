module Language.Edh.Meta.Analyze where

-- import Debug.Trace

import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import qualified Data.ByteString as B
import Data.Dynamic
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.List
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (Decoding (Some), streamDecodeUtf8With)
import Data.Text.Encoding.Error (lenientDecode)
import qualified Data.Vector as V
import GHC.Clock
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.EHI
import Language.Edh.Meta.AQ
import Language.Edh.Meta.AtTypes
import Language.Edh.Meta.Model
import Language.Edh.RtTypes
import Numeric.Search.Range
import System.Directory
import System.FilePath
import Prelude

el'LocateModule :: EL'World -> Text -> EdhProc EL'ModuSlot
el'LocateModule !elw !absModuSpec !exit !ets =
  if "." `T.isPrefixOf` nomSpec
    then
      throwEdh ets UsageError $
        "not a valid absolute Edh module spec: " <> absModuSpec
    else
      unsafeIOToSTM (locateEdhModule nomSpec ".") >>= \case
        Left !err -> throwEdh ets PackageError err
        Right (_moduPath, !moduFile) -> runEdhTx ets $
          el'LocateModuleByFile elw (T.pack moduFile) $ \ !ms _ets ->
            exitEdh ets exit ms
  where
    !nomSpec = normalizeImportSpec absModuSpec

el'LocateModuleByFile :: EL'World -> Text -> EdhProc EL'ModuSlot
el'LocateModuleByFile !elw !moduFile !exit !ets =
  runEdhTx ets $
    edhContIO $
      fsSearch >>= \case
        Left !err -> atomically $ throwEdh ets UsageError err
        Right (Left (!homePath, !scriptName, !absFile)) ->
          atomically (prepareHome homePath)
            -- with 2 separate STM txs
            >>= atomically
              . goWith
                scriptName
                absFile
                el'home'scripts
        Right (Right (!homePath, !moduName, !absFile)) ->
          atomically (prepareHome homePath)
            -- with 2 separate STM txs
            >>= atomically
              . goWith
                moduName
                absFile
                el'home'modules
  where
    goWith ::
      Text ->
      Text ->
      (EL'Home -> TMVar (Map.HashMap ModuleName EL'ModuSlot)) ->
      EL'Home ->
      STM ()
    goWith !name !absFile !mmField !home =
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
            !otfVar <- newTVar Nothing
            !parsing <- newEmptyTMVar
            !resolution <- newEmptyTMVar
            let !ms =
                  EL'ModuSlot
                    home
                    name
                    (SrcDoc absFile)
                    otfVar
                    parsing
                    resolution
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

    -- splitFileName leaves trailing / for dir, get rid of it
    splitDirFile :: FilePath -> (FilePath, FilePath)
    splitDirFile path = (takeDirectory dir, file)
      where
        (dir, file) = splitFileName path

    fsSearch ::
      IO
        ( Either
            Text
            ( Either
                (Text, ScriptName, Text)
                (Text, ModuleName, Text)
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
                        (Text, ScriptName, Text)
                        (Text, ModuleName, Text)
                    )
                )
            go (!dir, !relPath) = case splitDirFile dir of
              (!homeDir, "edh_modules") -> case splitDirFile relPath of
                (!moduName, "__main__.edh") ->
                  return $
                    Right $
                      Left
                        ( T.pack homeDir,
                          T.pack moduName,
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
                                  T.pack absFile
                                )
                (!moduName, "__include__.edh") ->
                  let !conflictingFile = dir </> moduName <> ".iedh"
                   in doesPathExist conflictingFile >>= \case
                        True ->
                          return $
                            Left $
                              "conflicting "
                                <> T.pack conflictingFile
                        False ->
                          return $
                            Right $
                              Left
                                ( T.pack homeDir,
                                  T.pack moduName,
                                  T.pack absFile
                                )
                _ -> case stripExtension ".edh" relPath of
                  Just !moduName ->
                    let !conflictingFile = dir </> moduName </> "__init__.edh"
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
                                    T.pack absFile
                                  )
                  Nothing -> case stripExtension ".iedh" relPath of
                    Just !fragName ->
                      let !conflictingFile =
                            dir </> fragName </> "__include__.edh"
                       in doesPathExist conflictingFile >>= \case
                            True ->
                              return $
                                Left $
                                  "conflicting "
                                    <> T.pack conflictingFile
                            False ->
                              return $
                                Right $
                                  Left
                                    ( T.pack homeDir,
                                      T.pack fragName,
                                      T.pack absFile
                                    )
                    Nothing ->
                      return $
                        Right $
                          Right
                            (T.pack homeDir, T.pack relPath, T.pack absFile)
              (!gpdir, !pdir) ->
                doesDirectoryExist (gpdir </> "edh_modules") >>= \case
                  False ->
                    if gpdir == dir -- reached fs root
                      then return $ Left "not in any edh home"
                      else go (gpdir, pdir </> relPath)
                  True ->
                    return $
                      Right $
                        Left
                          ( T.pack gpdir,
                            T.pack $ pdir </> relPath,
                            T.pack absFile
                          )
         in go $ splitDirFile absFile

el'LocateImportee ::
  EL'ModuSlot ->
  Text ->
  EL'Analysis (Either Text EL'ModuSlot)
el'LocateImportee !msFrom !impSpec !exit !eas =
  unsafeIOToSTM
    (locateEdhModule nomSpec $ edhRelativePathFrom $ T.unpack docFile)
    >>= \case
      Left !err -> el'Exit eas exit $ Left err
      Right (_moduPath, !moduFile) -> runEdhTx ets $
        el'LocateModuleByFile elw (T.pack moduFile) $ \ !ms _ets ->
          el'Exit eas exit $ Right ms
  where
    elw = el'world eas
    ets = el'ets eas
    SrcDoc !docFile = el'modu'doc msFrom
    !nomSpec = normalizeImportSpec impSpec

el'LocateIncludee ::
  EL'ModuSlot ->
  Text ->
  EL'Analysis (Either Text EL'ModuSlot)
el'LocateIncludee !msFrom !incSpec !exit !eas =
  unsafeIOToSTM
    (locateEdhFragment nomSpec $ edhRelativePathFrom $ T.unpack docFile)
    >>= \case
      Left !err -> el'Exit eas exit $ Left err
      Right (_moduPath, !moduFile) -> runEdhTx ets $
        el'LocateModuleByFile elw (T.pack moduFile) $ \ !ms _ets ->
          el'Exit eas exit $ Right ms
  where
    elw = el'world eas
    ets = el'ets eas
    SrcDoc !docFile = el'modu'doc msFrom
    !nomSpec = normalizeImportSpec incSpec

-- | walk through all diagnostics for a module, including all its dependencies
el'WalkResolutionDiags ::
  EL'ModuSlot ->
  (EL'ModuSlot -> [EL'Diagnostic] -> STM ()) ->
  STM ()
el'WalkResolutionDiags !msStart !walker = void $ go Map.empty msStart
  where
    walkDeps ::
      [(EL'ModuSlot, Bool)] ->
      HashMap Text Bool ->
      STM (HashMap Text Bool)
    walkDeps [] !vm = return vm
    walkDeps ((!dep, !hold) : rest) !vm =
      if hold
        then go vm dep >>= walkDeps rest
        else walkDeps rest vm
    go :: HashMap Text Bool -> EL'ModuSlot -> STM (HashMap Text Bool)
    go !vm !ms = case Map.lookup mk vm of
      Just {} -> return vm
      Nothing ->
        tryReadTMVar reso >>= \case
          Nothing -> return vm'
          Just (EL'ModuResolving !resolving _acts) -> do
            walker ms =<< readTVar (el'resolving'diags resolving)
            flip walkDeps vm' . Map.toList
              =<< readTVar (el'resolving'dependants resolving)
          Just (EL'ModuResolved !resolved) -> do
            walker ms $ el'resolution'diags resolved
            flip walkDeps vm' $ Map.toList $ el'modu'dependencies resolved
      where
        !reso = el'modu'resolution ms
        SrcDoc !mk = el'modu'doc ms
        vm' = Map.insert mk True vm

-- | walk through all diagnostics for a module, including all its dependencies
el'WalkParsingDiags ::
  EL'ModuSlot ->
  (EL'ModuSlot -> [EL'Diagnostic] -> STM ()) ->
  STM ()
el'WalkParsingDiags !msStart !walker = void $ go Map.empty msStart
  where
    walkDeps ::
      [(EL'ModuSlot, Bool)] ->
      HashMap Text Bool ->
      STM (HashMap Text Bool)
    walkDeps [] !vm = return vm
    walkDeps ((!dep, !hold) : rest) !vm =
      if hold
        then go vm dep >>= walkDeps rest
        else walkDeps rest vm
    go :: HashMap Text Bool -> EL'ModuSlot -> STM (HashMap Text Bool)
    go !vm !ms = case Map.lookup mk vm of
      Just {} -> return vm
      Nothing -> do
        tryReadTMVar pars >>= \case
          Just (EL'ModuParsed !parsed) -> walker ms $ el'parsing'diags parsed
          _ -> return ()
        tryReadTMVar reso >>= \case
          Nothing -> return vm'
          Just (EL'ModuResolving !resolving _resolvedVar) ->
            flip walkDeps vm' . Map.toList
              =<< readTVar (el'modu'dependencies'wip resolving)
          Just (EL'ModuResolved !resolved) ->
            flip walkDeps vm' $ Map.toList $ el'modu'dependencies resolved
      where
        !pars = el'modu'parsing ms
        !reso = el'modu'resolution ms
        SrcDoc !mk = el'modu'doc ms
        vm' = Map.insert mk True vm

-- | invalidate resolution results of this module and all known dependants
-- will have parsing result invaliated as well if `srcChanged` is @True@
el'InvalidateModule ::
  Bool ->
  EL'ModuSlot ->
  EdhProc ()
el'InvalidateModule !srcChgd !ms !exit !ets = do
  when srcChgd $ void $ tryTakeTMVar (el'modu'parsing ms)
  tryTakeTMVar reso >>= \case
    Nothing -> pure ()
    Just (EL'ModuResolving !resolving _acts) ->
      readTVar (el'resolving'dependants resolving)
        >>= invalidateDeps (el'resolving'dependants resolving) . Map.toList
    Just (EL'ModuResolved !resolved) ->
      readTVar (el'modu'dependants resolved)
        >>= invalidateDeps (el'modu'dependants resolved) . Map.toList
  exitEdh ets exit ()
  where
    !reso = el'modu'resolution ms
    invalidateDeps ::
      TVar (HashMap EL'ModuSlot Bool) ->
      [(EL'ModuSlot, Bool)] ->
      STM ()
    invalidateDeps !dependants !deps = go [] deps
      where
        go :: [(EL'ModuSlot, Bool)] -> [(EL'ModuSlot, Bool)] -> STM ()
        go !upds [] =
          unless (null upds) $
            modifyTVar' dependants $
              -- todo maybe should delete instead of update here?
              -- in case some module file is deleted, this'll leak?
              Map.union (Map.fromList upds)
        go !upds ((!dependant, !hold) : rest) =
          tryTakeTMVar (el'modu'resolution dependant) >>= \case
            Nothing -> go upds rest
            Just resolving@EL'ModuResolving {} -> do
              putTMVar (el'modu'resolution dependant) resolving
              go upds rest
            Just (EL'ModuResolved !resolved') ->
              case Map.lookup ms (el'modu'dependencies resolved') of
                Just True ->
                  runEdhTx ets $
                    el'InvalidateModule False dependant $ \_ _ets ->
                      go upds rest
                _ ->
                  if hold
                    then
                      go
                        ((dependant, False) : upds)
                        rest
                    else go upds rest

moduSrcStabilized :: EL'ModuSlot -> STM Bool
moduSrcStabilized !ms =
  readTVar otfVar >>= \case
    Nothing -> return True
    Just (_ver, _src, !otfTime) -> do
      !currTime <- unsafeIOToSTM getMonotonicTimeNSec
      -- considered stabilized after at least 3 seconds
      -- todo make this tunable?
      return $ currTime - otfTime >= 3000000000
  where
    !otfVar = el'modu'src'otf ms

-- | Obtain the result as the specified module is parsed
--
-- It is throttled wrt source changes on-the-fly, esp. during fast typing,
-- see:
--   https://github.com/emacs-lsp/lsp-mode/issues/362#issuecomment-446549480
asModuleParsed :: EL'ModuSlot -> EdhProc EL'ParsedModule
asModuleParsed !ms !exit !ets =
  moduSrcStabilized ms >>= \case
    False -> edhContIO'' ets $ do
      threadDelay 100000 -- check back after 0.1 second
      atomically $ asModuleParsed ms exit ets
    True -> do
      !otf <- readTVar otfVar
      let !otfVersion = case otf of
            Just (!ver, _, _) -> ver
            _ -> 0
          doParseModule :: (EL'ParsedModule -> STM ()) -> STM ()
          doParseModule !exit' = edhCatch ets doParse exit' $
            \ !etsCatching !exv !recover !rethrow -> case exv of
              EdhNil -> rethrow nil
              _ -> edhValueDesc etsCatching exv $ \ !exDesc ->
                recover $
                  EL'ParsedModule
                    otfVersion
                    NoDocCmt
                    []
                    [el'Diag el'Error noSrcRange "err-parse" exDesc]
            where
              doParse !exit'' !etsParse = do
                (!resultVersion, !moduSrc, _) <- case otf of
                  Just !otfSrc -> return otfSrc
                  Nothing ->
                    let SrcDoc !moduFile = moduDoc
                     in unsafeIOToSTM
                          ( streamDecodeUtf8With lenientDecode
                              <$> B.readFile (T.unpack moduFile)
                          )
                          >>= \case
                            Some !src _ _ -> return (0, src, 0)
                parseModuleSource resultVersion moduSrc moduDoc exit'' etsParse
          goParse = do
            -- STM can retry back to re-check, in case parsingVar has been
            -- changed by others concurrently, so duplicate parsing effort
            -- can be avoided
            void $ tryTakeTMVar parsingVar
            !parsedVar <- newEmptyTMVar
            putTMVar parsingVar (EL'ModuParsing otfVersion parsedVar)
            -- schedule the parsing to happen in next tx, so retries caused by
            -- above don't include the expensive, actual parsing
            edhContSTM'' ets $
              -- todo
              --  maybe try harder to guarantee 'parsedVar' will always be
              --  filled. bracket with STM monad is not correct as multiple txs
              --  it will span; using Edh finally block may be the way, but
              --  we're already doing that in 'doParseModule', not sure
              --  anything to be done here so.
              doParseModule $ \ !parsed -> do
                -- clear the otf src after successfully parsed
                writeTVar otfVar Nothing
                -- install the parsed record
                putTMVar parsedVar parsed
                tryTakeTMVar parsingVar >>= \case
                  Just (EL'ModuParsing !parsingVer _parsedVar')
                    | otfVersion >= parsingVer ->
                      -- the most expected scenario, we got the latest result
                      putTMVar parsingVar $ EL'ModuParsed parsed
                  Just !other ->
                    -- invalidated & new analysation wip
                    void $ tryPutTMVar parsingVar other
                  Nothing ->
                    -- invalidated meanwhile
                    return ()

                -- return from this procedure
                exitEdh ets exit parsed

      tryReadTMVar parsingVar >>= \case
        Nothing -> goParse
        Just (EL'ModuParsing !parsingVer !parsedVar) ->
          if otfVersion > parsingVer
            then goParse
            else
              runEdhTx ets $
                -- parsing by some other thread,
                -- blocking wait a result in next tx
                edhContSTM $ readTMVar parsedVar >>= exitEdh ets exit
        Just (EL'ModuParsed !parsed) ->
          if otfVersion > el'modu'src'version parsed
            then goParse
            else exitEdh ets exit parsed
  where
    !moduDoc = el'modu'doc ms
    !otfVar = el'modu'src'otf ms
    !parsingVar = el'modu'parsing ms

-- | Fill in module source on the fly, usually pending save from an IDE editor,
-- return whether this is the first fill since last parsed.
el'FillModuleSource :: Int -> Text -> EL'ModuSlot -> EdhProc Bool
el'FillModuleSource !docVersion !moduSource !ms !exit !ets =
  runEdhTx ets $
    el'InvalidateModule True ms $ \() _ets -> do
      !prevFill <- readTVar otfVar
      !otfTime <- unsafeIOToSTM getMonotonicTimeNSec
      writeTVar otfVar $ Just (docVersion, moduSource, otfTime)
      exitEdh ets exit $ case prevFill of
        Nothing -> True
        _ -> False
  where
    otfVar = el'modu'src'otf ms

parseModuleSource :: Int -> Text -> SrcDoc -> EdhProc EL'ParsedModule
parseModuleSource !srcVersion !moduSource (SrcDoc !moduFile) !exit !ets =
  runEdhTx ets $
    edhContIO $
      parseEdh world moduFile moduSource
        >>= \case
          Left !err -> atomically $ do
            let !msg = T.pack $ errorBundlePretty err
                !edhWrapException = edh'exception'wrapper world
                !edhErr =
                  EdhError ParseError msg (toDyn nil) $ getEdhErrCtx 0 ets
            edhWrapException (Just ets) (toException edhErr)
              >>= \ !exo -> edhThrow ets (EdhObject exo)
          Right (!stmts, !docCmt) ->
            atomically $
              exitEdh ets exit $ EL'ParsedModule srcVersion docCmt stmts []
  where
    !world = edh'prog'world $ edh'thread'prog ets

-- | obtain the result as the specified module is resolved
asModuleResolved :: EL'World -> EL'ModuSlot -> EdhProc EL'ResolvedModule
asModuleResolved !world !ms !exit =
  asModuleResolving world ms $ \case
    EL'ModuResolving _resolving !resolvedVar -> \ !ets ->
      -- blocking wait a result in next tx
      runEdhTx ets $ edhContSTM $ readTMVar resolvedVar >>= exitEdh ets exit
    EL'ModuResolved !resolved -> exitEdhTx exit resolved

asModuleResolving :: EL'World -> EL'ModuSlot -> EdhProc EL'ModuResolution
asModuleResolving !world !ms !exit !ets = do
  !thId <- unsafeIOToSTM myThreadId
  tryReadTMVar resoVar >>= \case
    Just reso@(EL'ModuResolving !resolving !resolvedVar) ->
      if thId == el'resolving'thread resolving
        then -- resolving synchronously by this thread, to wait is to deadlock
          exitEdh ets exit reso
        else -- resolving by another thread, let's wait its result
          readTMVar resolvedVar >>= exitEdh ets exit . EL'ModuResolved
    Just !reso -> exitEdh ets exit reso
    Nothing -> do
      !resolvedVar <- newEmptyTMVar
      !exts <- newTVar []
      !exps <- iopdEmpty
      !dependencies <- newTVar Map.empty
      !diags <- newTVar []
      !dependants <- newTVar Map.empty
      let !resolving =
            EL'ResolvingModu
              thId
              exts
              exps
              dependencies
              diags
              dependants
      -- this put will retry back to re-check, if resoVar has been changed
      -- by others concurrently, so duplicate resolution effort can be avoided
      putTMVar resoVar (EL'ModuResolving resolving resolvedVar)
      -- schedule the resolution to happen in next tx, so retries caused by
      -- above don't include the expensive, actual resolution
      edhContSTM'' ets $
        -- todo
        -- maybe try harder to guarantee 'resolvedVar' will always be filled.
        -- bracket with STM monad is not correct as multiple txs it will span;
        -- using Edh finally block may be the way, but we're already doing that
        -- in 'doResolveModule', not sure anything to be done here so.
        doResolveModule resolving $ \ !resolved -> do
          -- install the resolved record
          putTMVar resolvedVar resolved
          tryTakeTMVar resoVar >>= \case
            Just (EL'ModuResolving _resolving resolvedVar')
              | resolvedVar' == resolvedVar ->
                -- the most expected scenario
                putTMVar resoVar $ EL'ModuResolved resolved
            Just !other ->
              -- invalidated & new analysation wip
              void $ tryPutTMVar resoVar other
            _ ->
              -- invalidated meanwhile
              return ()

          -- return from this procedure
          exitEdh ets exit $ EL'ModuResolved resolved
  where
    !resoVar = el'modu'resolution ms

    doResolveModule ::
      EL'ResolvingModu ->
      (EL'ResolvedModule -> STM ()) ->
      STM ()
    doResolveModule !resolving !exit' = runEdhTx ets $
      asModuleParsed ms $ \ !parsed _ets -> edhCatch
        ets
        (resolveParsedModule world ms resolving $ el'modu'stmts parsed)
        exit'
        $ \ !etsCatching !exv !recover !rethrow -> case exv of
          EdhNil -> rethrow nil
          _ -> edhValueDesc etsCatching exv $ \ !exDesc ->
            recover $
              EL'ResolvedModule
                ( EL'Scope
                    noSrcRange
                    V.empty
                    V.empty
                )
                odEmpty
                V.empty
                V.empty
                [ el'Diag
                    el'Error
                    noSrcRange
                    "resolve-err"
                    exDesc
                ]
                Map.empty
                (el'resolving'dependants resolving)

resolveParsedModule ::
  EL'World ->
  EL'ModuSlot ->
  EL'ResolvingModu ->
  [StmtSrc] ->
  EdhProc EL'ResolvedModule
resolveParsedModule !world !ms !resolving !body !exit !ets = do
  !aqv <- newTVar []
  let !modu'name = el'modu'name ms
      !name'def =
        EL'AttrDef
          (AttrByName "__name__")
          (DocCmt ["import name of current module"])
          "<module>"
          noSrcRange
          (ExprSrc (LitExpr (StringLiteral modu'name)) noSrcRange)
          (EL'Const (EdhString modu'name))
          maoAnnotation
          Nothing
      SrcDoc !modu'file = el'modu'doc ms
      !modu'path = case T.stripSuffix "/__init__.edh" modu'file of
        Just !path -> path
        Nothing -> case T.stripSuffix "/__main__.edh" modu'file of
          Just !path -> path
          Nothing -> case T.stripSuffix "/__include__.edh" modu'file of
            Just !path -> path
            Nothing -> case T.stripSuffix ".edh" modu'file of
              Just !path -> path
              Nothing -> case T.stripSuffix ".iedh" modu'file of
                Just !path -> path
                Nothing -> modu'file
      !file'def =
        EL'AttrDef
          (AttrByName "__file__")
          (DocCmt ["absolute path of current module's source file"])
          "<module>"
          noSrcRange
          (ExprSrc (LitExpr (StringLiteral modu'file)) noSrcRange)
          (EL'Const (EdhString modu'file))
          maoAnnotation
          Nothing
      !path'def =
        EL'AttrDef
          (AttrByName "__path__")
          ( DocCmt
              [ "absolute path of the directory containing current module's"
                  <> " source file"
              ]
          )
          "<module>"
          noSrcRange
          (ExprSrc (LitExpr (StringLiteral modu'path)) noSrcRange)
          (EL'Const (EdhString modu'path))
          maoAnnotation
          Nothing
      !builtinAttrs =
        odFromList $
          (\ !def -> (el'attr'def'key def, def))
            <$> [name'def, file'def, path'def]
  !ctxDefs <- newTVar []
  !ctxRefs <- newTVar []
  !branchAttrs <- iopdFromList $ odToList builtinAttrs
  !moduAttrs <- iopdClone branchAttrs
  !moduEffs <- iopdEmpty
  !moduAnnos <- iopdEmpty
  !branchRegions <- newTVar [EL'Region beginningSrcPos builtinAttrs]
  !moduScopes <- newTVar []
  !moduRegions <- newTVar []
  !docCmtVar <- newTVar NoDocCmt
  let !moduObj =
        EL'Object
          el'ModuleClass
          moduAttrs
          (el'modu'exts'wip resolving)
          (el'modu'exps'wip resolving)
      !bwip =
        EL'BranchWIP
          branchAttrs
          moduEffs
          moduAnnos
          branchRegions
      !pwip =
        EL'ProcWIP
          bwip
          moduAttrs
          moduObj
          moduScopes
          moduRegions
      !eac =
        EL'Context
          { el'ctx'scope = EL'InitModule ms resolving pwip,
            el'ctx'outers = [],
            el'ctx'pure = False,
            el'ctx'exporting = False,
            el'ctx'eff'defining = False,
            el'ctx'attr'defs = ctxDefs,
            el'ctx'attr'refs = ctxRefs,
            el'ctx'diags = el'resolving'diags resolving
          }
      !eas =
        EL'AnalysisState
          { el'world = world,
            el'ana'queue = aqv,
            el'context = eac,
            el'doc'cmt = docCmtVar,
            el'ets = ets
          }

  el'RunTx eas $
    el'AnalyzeStmts body $ \_ !easDone -> el'PerformAnalysis aqv $ do
      let !eacDone = el'context easDone
          !swipDone = el'ctx'scope eacDone
          !pwipDone = el'ProcWIP swipDone
          !bwipDone = el'scope'branch'wip pwipDone
      !regions'wip <- readTVar (el'branch'regions'wip bwipDone)
      !innerScopes <- readTVar moduScopes
      !regions <-
        (regions'wip ++)
          <$> readTVar (el'scope'regions'wip pwipDone)
      !modu'attr'defs <- sortOn attrDefKey <$> readTVar ctxDefs
      !modu'attr'refs <- sortOn attrRefKey <$> readTVar ctxRefs

      !diags <- readTVar $ el'resolving'diags resolving
      !moduExps <- iopdSnapshot $ el'modu'exps'wip resolving
      !dependencies <- readTVar $ el'modu'dependencies'wip resolving
      let !el'scope =
            EL'Scope
              { el'scope'span = SrcRange beginningSrcPos (SrcPos (-1) (-1)),
                el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                el'scope'regions = V.fromList $ sortOn regionKey regions
              }
      exitEdh ets exit $
        EL'ResolvedModule
          el'scope
          moduExps
          (V.fromList modu'attr'defs)
          (V.fromList modu'attr'refs)
          (reverse diags)
          dependencies
          (el'resolving'dependants resolving)

-- | pack arguments
el'PackArgs :: ArgsPacker -> EL'Analysis EL'ArgsPack
el'PackArgs (ArgsPacker !argSndrs _) !exit !eas =
  el'RunTx easPure $ collectArgs [] [] False False argSndrs
  where
    !eac = el'context eas
    !easPure = eas {el'context = eac {el'ctx'pure = True}}
    !originPure = el'ctx'pure eac

    collectArgs ::
      [EL'Value] ->
      [(AttrKey, EL'Value)] ->
      Bool ->
      Bool ->
      [ArgSender] ->
      EL'Tx
    collectArgs !args !kwargs !dyn'args !dyn'kwargs [] = \ !easDone ->
      el'Exit
        easDone
          { el'context = (el'context easDone) {el'ctx'pure = originPure}
          }
        exit
        $ EL'ArgsPack
          (reverse args)
          (odFromList $ reverse kwargs)
          dyn'args
          dyn'kwargs
    collectArgs !args !kwargs !dyn'args !dyn'kwargs (asndr : rest) =
      case asndr of
        UnpackPosArgs !ax -> el'AnalyzeExpr ax $ \_argVal ->
          -- TODO try analyze the unpacking
          collectArgs args kwargs True dyn'kwargs rest
        UnpackKwArgs !ax -> el'AnalyzeExpr ax $ \_argVal ->
          -- TODO try analyze the unpacking
          collectArgs args kwargs dyn'args True rest
        UnpackPkArgs !ax -> el'AnalyzeExpr ax $ \_argVal ->
          -- TODO try analyze the unpacking
          collectArgs args kwargs True True rest
        SendPosArg !ax -> el'AnalyzeExpr ax $ \ !argVal ->
          collectArgs (argVal : args) kwargs dyn'args dyn'kwargs rest
        SendKwArg !argAddr !ax -> \ !easDone ->
          el'ResolveAttrAddr easDone argAddr $ \case
            Nothing ->
              el'RunTx easDone $
                collectArgs args kwargs dyn'args dyn'kwargs rest
            Just !argKey -> el'RunTx easDone $
              el'AnalyzeExpr ax $ \ !argVal ->
                collectArgs
                  args
                  ((argKey, argVal) : kwargs)
                  dyn'args
                  dyn'kwargs
                  rest

-- * statement analysis

-- | a sequence of statements
el'AnalyzeStmts :: [StmtSrc] -> EL'Analysis EL'Value
-- note eas should be passed alone the sequence of statements, for regions to
-- be handled properly
el'AnalyzeStmts !stmts !exit = go stmts
  where
    go :: [StmtSrc] -> EL'Tx
    go [] = el'ExitTx exit $ EL'Const nil
    go [!stmt] = el'AnalyzeStmt stmt exit
    go (stmt : rest) = el'AnalyzeStmt stmt $ const $ go rest

-- | analyze a statement in context
el'AnalyzeStmt :: StmtSrc -> EL'Analysis EL'Value
--

-- a standalone expression
el'AnalyzeStmt (StmtSrc (ExprStmt !expr !docCmt) !stmt'span) !exit !eas = do
  writeTVar (el'doc'cmt eas) docCmt
  el'RunTx eas $ el'AnalyzeExpr (ExprSrc expr stmt'span) exit
--

-- a let statement
el'AnalyzeStmt
  let'stmt@(StmtSrc (LetStmt !argsRcvr !argsSndr) !stmt'span)
  !exit
  !eas = case argsSndr of
    ArgsPacker [SendPosArg !singleArg] apk'span -> el'RunTx eas $
      el'AnalyzeExpr singleArg $ \ !singleVal _eas -> case singleVal of
        EL'Apk !apk -> doRecv apk
        _ -> case argsRcvr of
          SingleReceiver (RecvRestPkArgs !addr) ->
            -- wild repacking
            recvOne addr $ EL'Apk $ EL'ArgsPack [singleVal] odEmpty False False
          SingleReceiver
            ( RecvArg
                addr@(AttrAddrSrc _ arg'span)
                !maybeRename
                _maybeDef
              ) -> do
              case maybeRename of
                Nothing -> recvOne addr singleVal
                Just (DirectRef !addr') -> recvOne addr' singleVal
                Just IndirectRef {} -> pure () -- TODO define art into objs
                _ -> do
                  el'LogDiag
                    diags
                    el'Error
                    arg'span
                    "invalid-target"
                    "invalid let target"
              el'Exit eas exit $ EL'Const nil
          SingleReceiver !rcvr -> do
            el'LogDiag
              diags
              el'Warning
              (argReceiverSpan rcvr)
              "strange-single-rcvr"
              "strange single arg receiver"
            doUnknownRcvrs [rcvr]
          PackReceiver !rcvrs _rcvrs'span -> do
            el'LogDiag
              diags
              el'Warning
              apk'span
              "dynamic-unpack"
              "els does not analyze source structure of dynamic unpacking yet"
            doUnknownRcvrs rcvrs
          WildReceiver _ -> el'Exit eas exit $ EL'Const nil
          NullaryReceiver ->
            -- TODO this possible at all?
            el'Exit eas exit $ EL'Const nil
    _ -> el'RunTx eas $ el'PackArgs argsSndr $ \ !apk _eas -> doRecv apk
    where
      {- HLINT ignore "Reduce duplication" -}
      !eac = el'context eas
      diags = el'ctx'diags eac
      !swip = el'ctx'scope eac
      !pwip = el'ProcWIP swip
      !bwip = el'scope'branch'wip pwip

      unknownVal = EL'Expr $ ExprSrc (LitExpr NilLiteral) stmt'span

      doUnknownRcvrs :: [ArgReceiver] -> STM ()
      doUnknownRcvrs [] = el'Exit eas exit $ EL'Const nil
      doUnknownRcvrs (rcvr : rest) = do
        case rcvr of
          RecvRestPosArgs !addr ->
            recvOne addr $ EL'Apk $ EL'ArgsPack [] odEmpty True False
          RecvRestKwArgs !addr ->
            recvOne addr $ EL'Apk $ EL'ArgsPack [] odEmpty False True
          RecvRestPkArgs !addr ->
            recvOne addr $ EL'Apk $ EL'ArgsPack [] odEmpty True True
          RecvArg addr@(AttrAddrSrc _ arg'span) !maybeRename _maybeDef ->
            case maybeRename of
              Nothing -> recvOne addr unknownVal
              Just (DirectRef !addr') -> recvOne addr' unknownVal
              Just IndirectRef {} -> pure () -- TODO define art into objs
              _ -> do
                el'LogDiag
                  diags
                  el'Error
                  arg'span
                  "invalid-target"
                  "invalid let target"
        doUnknownRcvrs rest

      recvOne :: AttrAddrSrc -> EL'Value -> STM ()
      recvOne (AttrAddrSrc (NamedAttr "_") _) _ = pure ()
      recvOne addr@(AttrAddrSrc _ !addr'span) !v =
        el'ResolveAttrAddr eas addr $ \case
          Nothing -> return ()
          Just !k -> recvOne' addr'span k v

      recvOne' :: SrcRange -> AttrKey -> EL'Value -> STM ()
      recvOne' !focus'span !attrKey !attrVal = do
        !attrAnno <- newTVar =<< iopdLookup attrKey (el'branch'annos'wip bwip)
        !prevDef <-
          iopdLookup attrKey $
            if el'ctx'eff'defining eac
              then el'branch'effs'wip bwip
              else el'branch'attrs'wip bwip
        let !attrDef =
              EL'AttrDef
                attrKey
                NoDocCmt
                "<let>"
                focus'span
                (ExprSrc (BlockExpr [let'stmt]) stmt'span)
                attrVal
                attrAnno
                prevDef
        -- record as definition symbol
        recordAttrDef eac attrDef
        if el'ctx'eff'defining eac
          then do
            let !effs = el'branch'effs'wip bwip
            case attrVal of
              EL'Const EdhNil -> iopdDelete attrKey effs
              _ -> iopdInsert attrKey attrDef effs
          else do
            let !attrs = el'branch'attrs'wip bwip
            case attrVal of
              EL'Const EdhNil -> iopdDelete attrKey attrs
              _ -> iopdInsert attrKey attrDef attrs
        when (el'ctx'exporting eac) $
          iopdInsert attrKey attrDef $ el'obj'exps $ el'scope'this'obj pwip

      doRecv :: EL'ArgsPack -> STM ()
      doRecv apk@(EL'ArgsPack !args !kwargs _dyn'args _dyn'kwargs) =
        case argsRcvr of
          PackReceiver !rcvrs _ -> doRcvrs apk rcvrs
          SingleReceiver !rcvr -> doRcvrs apk [rcvr]
          NullaryReceiver -> doRcvrs apk []
          WildReceiver !rcvr'span -> do
            unless (null args) $
              el'LogDiag
                diags
                el'Error
                rcvr'span
                "let-wild-pos-arg"
                "letting positional argument(s) into wild receiver"

            -- receive each kwargs
            forM_ (odToList kwargs) $ \(!k, !v) -> recvOne' stmt'span k v

            -- record a region after this let statement, for current branch
            iopdSnapshot (el'branch'attrs'wip bwip)
              >>= modifyTVar' (el'branch'regions'wip bwip) . (:)
                . EL'Region (src'end stmt'span)

            el'Exit eas exit $ EL'Const nil

      doRcvrs :: EL'ArgsPack -> [ArgReceiver] -> STM ()
      doRcvrs (EL'ArgsPack !all'args !all'kwargs !dyn'args !dyn'kwargs) !rcvrs =
        go all'args all'kwargs rcvrs $ \ !args' !kwargs' -> do
          unless (null args' && odNull kwargs') $
            el'LogDiag
              diags
              el'Error
              stmt'span
              "extra-args"
              "extraneous arguments not consumed"

          -- record a region after this let statement, for current scope
          iopdSnapshot (el'branch'attrs'wip bwip)
            >>= modifyTVar' (el'branch'regions'wip bwip) . (:)
              . EL'Region (src'end stmt'span)

          el'Exit eas exit $ EL'Const nil
        where
          go ::
            [EL'Value] ->
            OrderedDict AttrKey EL'Value ->
            [ArgReceiver] ->
            ([EL'Value] -> OrderedDict AttrKey EL'Value -> STM ()) ->
            STM ()
          go !args !kwargs [] !done = done args kwargs
          go !args !kwargs (rcvr : rest) done =
            recvFromPack args kwargs rcvr $ \ !args' !kwargs' ->
              go args' kwargs' rest done

          recvFromPack ::
            [EL'Value] ->
            OrderedDict AttrKey EL'Value ->
            ArgReceiver ->
            ([EL'Value] -> OrderedDict AttrKey EL'Value -> STM ()) ->
            STM ()
          recvFromPack !args !kwargs !rcvr !done = case rcvr of
            RecvRestPosArgs !addr -> do
              recvOne addr $ EL'Apk $ EL'ArgsPack args odEmpty True False
              done [] kwargs
            RecvRestKwArgs !addr -> do
              recvOne addr $ EL'Apk $ EL'ArgsPack [] kwargs False True
              done args odEmpty
            RecvRestPkArgs !addr -> do
              recvOne addr $ EL'Apk $ EL'ArgsPack args kwargs True True
              done [] odEmpty
            RecvArg addr@(AttrAddrSrc _ arg'span) !maybeRename maybeDef ->
              let goRecv :: (AttrKey -> EL'Value -> STM ()) -> STM ()
                  goRecv !received =
                    el'ResolveAttrAddr eas addr $ \case
                      Nothing -> done args kwargs
                      Just !recvKey -> case odTakeOut recvKey kwargs of
                        (Just !kwVal, kwargs') -> do
                          received recvKey kwVal
                          done args kwargs'
                        (Nothing, kwargs') -> case args of
                          argVal : args' -> do
                            received recvKey argVal
                            done args' kwargs'
                          _ -> case maybeDef of
                            Nothing -> do
                              if dyn'args || dyn'kwargs
                                then
                                  el'LogDiag
                                    diags
                                    el'Warning
                                    arg'span
                                    "dyn-missing-arg"
                                    "possible missing argument"
                                else
                                  el'LogDiag
                                    diags
                                    el'Error
                                    arg'span
                                    "missing-arg"
                                    "missing argument"
                              received recvKey $
                                EL'Expr $
                                  ExprSrc (AttrExpr $ DirectRef addr) arg'span
                              done args kwargs
                            Just !defExpr -> el'RunTx
                              eas {el'context = eac {el'ctx'pure = True}}
                              $ el'AnalyzeExpr defExpr $
                                \ !defVal _eas -> do
                                  received recvKey defVal
                                  done args kwargs
               in case maybeRename of
                    Nothing -> goRecv $ recvOne' arg'span
                    Just (DirectRef !addr') ->
                      goRecv $ \_recvKey -> recvOne addr'
                    Just IndirectRef {} -> done args kwargs
                    _ -> do
                      el'LogDiag
                        diags
                        el'Error
                        arg'span
                        "invalid-target"
                        "invalid let target"
                      done args kwargs

--

-- effect defining
el'AnalyzeStmt (StmtSrc (EffectStmt !effs !docCmt) _stmt'span) !exit !eas = do
  writeTVar (el'doc'cmt eas) docCmt
  el'RunTx eas {el'context = eac {el'ctx'eff'defining = True}} $
    el'AnalyzeExpr effs $ \_ _eas -> el'Exit eas exit $ EL'Const nil
  where
    !eac = el'context eas
--

-- extending
el'AnalyzeStmt
  (StmtSrc (ExtendsStmt superExpr@(ExprSrc _ !super'span)) _)
  !exit
  !eas =
    el'RunTx eas $
      el'AnalyzeExpr superExpr $ \ !superVal ->
        case el'UltimateValue superVal of
          EL'ObjVal {} -> \_eas -> do
            modifyTVar' exts (++ [superVal])
            el'Exit eas exit $ EL'Const nil
          EL'ClsVal {} -> \_eas -> do
            modifyTVar' exts (++ [superVal])
            el'Exit eas exit $ EL'Const nil
          EL'Apk (EL'ArgsPack !superVals !kwargs _dyn'args _dyn'kwargs)
            | odNull kwargs -> \_eas -> do
              forM_ superVals $ \ !superVal' ->
                case el'UltimateValue superVal' of
                  EL'ObjVal {} -> return ()
                  EL'ClsVal {} -> return ()
                  _ ->
                    el'LogDiag
                      diags
                      el'Warning
                      super'span
                      "invalid-super"
                      $ "invalid super object: " <> T.pack (show superVal')
              modifyTVar' exts (++ superVals)
              el'Exit eas exit $ EL'Const nil
          _ -> \_eas -> do
            el'LogDiag
              diags
              el'Warning
              super'span
              "invalid-super"
              $ "invalid super object: " <> T.pack (show superVal)
            modifyTVar' exts (++ [superVal]) -- TODO this toxic?
            el'Exit eas exit $ EL'Const nil
    where
      !eac = el'context eas
      diags = el'ctx'diags eac
      !swip = el'ctx'scope eac
      !pwip = el'ProcWIP swip
      !exts = el'obj'exts $ el'scope'this'obj pwip
--

-- go
el'AnalyzeStmt (StmtSrc (GoStmt !expr) _stmt'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr expr $ const $ el'ExitTx exit $ EL'Const nil
--

-- defer
el'AnalyzeStmt (StmtSrc (DeferStmt !expr) _stmt'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr expr $ const $ el'ExitTx exit $ EL'Const nil
--

-- perceive
el'AnalyzeStmt (StmtSrc (PerceiveStmt !expr !body) _stmt'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr expr $
      const $
        el'AnalyzeStmt body $
          const $ el'ExitTx exit $ EL'Const nil
--

-- continue
el'AnalyzeStmt (StmtSrc ContinueStmt _stmt'span) !exit !eas =
  el'Exit eas exit $ EL'Const EdhContinue
--

-- break
el'AnalyzeStmt (StmtSrc BreakStmt _stmt'span) !exit !eas =
  el'Exit eas exit $ EL'Const EdhBreak
--

-- fallthrough
el'AnalyzeStmt (StmtSrc FallthroughStmt _stmt'span) !exit !eas =
  el'Exit eas exit $ EL'Const EdhFallthrough
--

-- return
el'AnalyzeStmt (StmtSrc (ReturnStmt !expr !docCmt) _stmt'span) !exit !eas = do
  writeTVar (el'doc'cmt eas) docCmt
  el'RunTx eas $
    el'AnalyzeExpr expr $
      el'ExitTx exit . EL'Return
--

-- throw
el'AnalyzeStmt (StmtSrc (ThrowStmt !expr) _stmt'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr expr $
      el'ExitTx exit . EL'Throw
--

-- rethrow
el'AnalyzeStmt (StmtSrc RethrowStmt _stmt'span) !exit !eas =
  el'Exit eas exit EL'Rethrow
--

-- parse error
el'AnalyzeStmt
  (StmtSrc (IllegalSegment !errMsg !errPos) !stmt'span)
  !exit
  !eas = do
    el'LogDiag
      diags
      el'Error
      stmt'span {src'end = errPos}
      "illegal-code"
      errMsg
    el'Exit eas exit $ EL'Const nil
    where
      eac = el'context eas
      diags = el'ctx'diags eac
--

-- the rest of statements not analyzed
el'AnalyzeStmt _stmt !exit !eas = el'Exit eas exit $ EL'Const nil

-- * expression analysis

-- | literal to analysis time value
el'LiteralValue :: Literal -> STM EL'Value
el'LiteralValue = \case
  DecLiteral !v -> return $ EL'Const (EdhDecimal v)
  StringLiteral !v -> return $ EL'Const (EdhString v)
  BoolLiteral !v -> return $ EL'Const (EdhBool v)
  NilLiteral -> return $ EL'Const nil
  SinkCtor -> EL'Const . EdhEvs <$> newEdhSink
  ValueLiteral !v -> return $ EL'Const v

-- | analyze a sequence of expressions in pure context
el'AnalyzeExprs :: [ExprSrc] -> EL'Analysis [EL'Value]
-- note eas should be passed alone the sequence of expressions, for regions to
-- be handled properly
el'AnalyzeExprs [] !exit !eas = el'Exit eas exit []
el'AnalyzeExprs !exprs !exit !eas = el'RunTx easPure $ go exprs []
  where
    !eac = el'context eas
    !easPure = eas {el'context = eac {el'ctx'pure = True}}
    !originPure = el'ctx'pure eac

    go :: [ExprSrc] -> [EL'Value] -> EL'Tx
    go [] _ = error "bug: impossible"
    go [!expr] !vals = el'AnalyzeExpr expr $ \ !result !easDone ->
      el'Exit
        easDone
          { el'context = (el'context easDone) {el'ctx'pure = originPure}
          }
        exit
        $! reverse
        $ result : vals
    go (expr : rest) !vals = el'AnalyzeExpr expr $ \ !r ->
      go rest (r : vals)

el'ResolveAttrAddr ::
  EL'AnalysisState ->
  AttrAddrSrc ->
  (Maybe AttrKey -> STM ()) ->
  STM ()
el'ResolveAttrAddr _ (AttrAddrSrc (NamedAttr !attrName) _) !exit =
  exit $ Just $ AttrByName attrName
el'ResolveAttrAddr _ (AttrAddrSrc (QuaintAttr !attrName) _) !exit =
  exit $ Just $ AttrByName attrName
el'ResolveAttrAddr !eas (AttrAddrSrc (SymbolicAttr !symName) !addr'span) !exit =
  el'ResolveContextAttr eas (AttrByName symName) >>= \case
    Nothing -> do
      el'LogDiag
        diags
        el'Error
        addr'span
        "bad-attr-ref"
        "no such attribute defined"
      exit Nothing
    Just !def -> case el'UltimateValue $ el'attr'def'value def of
      EL'Const (EdhSymbol !symKey) -> exit $ Just $ AttrBySym symKey
      EL'Const (EdhString !nameKey) -> exit $ Just $ AttrByName nameKey
      _ -> do
        el'LogDiag
          diags
          el'Warning
          addr'span
          "dyn-attr-ref"
          "dynamic attribute reference"
        !dynSym <- mkSymbol "<dynamic-attr-key>"
        exit $ Just $ AttrBySym dynSym
  where
    eac = el'context eas
    diags = el'ctx'diags eac
el'ResolveAttrAddr !eas (AttrAddrSrc (IntplSymAttr _src !x) !addr'span) !exit =
  el'RunTx eas $
    el'AnalyzeExpr x $ \ !symVal _eas -> case symVal of
      EL'Const (EdhSymbol !symKey) -> exit $ Just $ AttrBySym symKey
      EL'Const (EdhString !nameKey) -> exit $ Just $ AttrByName nameKey
      _ -> do
        el'LogDiag
          diags
          el'Warning
          addr'span
          "dyn-attr-ref"
          "dynamic attribute reference"
        !dynSym <- mkSymbol "<dynamic-attr-key>"
        exit $ Just $ AttrBySym dynSym
  where
    eac = el'context eas
    diags = el'ctx'diags eac
el'ResolveAttrAddr _ (AttrAddrSrc (LitSymAttr !sym) _) !exit =
  exit $ Just $ AttrBySym sym
el'ResolveAttrAddr !eas (AttrAddrSrc MissedAttrName !addr'span) !exit = do
  el'LogDiag
    (el'ctx'diags $ el'context eas)
    el'Error
    addr'span
    "missing-attr"
    "missing attribute name"
  exit Nothing
el'ResolveAttrAddr !eas (AttrAddrSrc MissedAttrSymbol !addr'span) !exit = do
  el'LogDiag
    (el'ctx'diags $ el'context eas)
    el'Error
    addr'span
    "missing-sym"
    "missing symbolic attribute name"
  exit Nothing

-- | analyze an expression in context
el'AnalyzeExpr :: ExprSrc -> EL'Analysis EL'Value
--

-- block
el'AnalyzeExpr (ExprSrc (BlockExpr !stmts) !blk'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeStmts stmts $ \ !blkResult !easDone -> do
      let closeBlk = do
            let !eacDone = el'context easDone
                !swipDone = el'ctx'scope eacDone
                !pwipDone = el'ProcWIP swipDone
                !bwipDone = el'scope'branch'wip pwipDone
            -- close all pending regions
            !regions'wip <- swapTVar (el'branch'regions'wip bwipDone) []
            modifyTVar' (el'scope'regions'wip pwipDone) (regions'wip ++)

            el'Exit eas exit blkResult

      case blkResult of
        EL'Return {} -> closeBlk
        EL'Throw {} -> closeBlk
        EL'Rethrow -> closeBlk
        _ -> do
          let !eacDone = el'context easDone
              !swipDone = el'ctx'scope eacDone
              !pwipDone = el'ProcWIP swipDone
              !bwipDone = el'scope'branch'wip pwipDone
              !scope'attrs = el'scope'attrs'wip pwipDone
              !branch'attrs = el'branch'attrs'wip bwipDone
          !bas <- iopdSize branch'attrs
          -- merge all scope attrs into branch attrs
          flip iopdUpdate branch'attrs =<< iopdToList scope'attrs
          !bas' <- iopdSize branch'attrs
          when (bas' /= bas) $ do
            -- record a new region following this block as attrs changed
            !attrs <- iopdSnapshot branch'attrs
            modifyTVar'
              (el'branch'regions'wip bwipDone)
              (EL'Region (src'end blk'span) attrs :)

          el'Exit easDone exit blkResult
--

-- direct attribute addressing
el'AnalyzeExpr
  xsrc@( ExprSrc
           (AttrExpr (DirectRef addr@(AttrAddrSrc _ !addr'span)))
           _expr'span
         )
  !exit
  !eas =
    el'ResolveAttrAddr eas addr $ \case
      Nothing -> returnAsExpr -- error diag should have been logged
      Just (AttrByName "_") -> do
        el'LogDiag
          diags
          el'Error
          addr'span
          "underscore-ref"
          "referencing underscore"
        el'Exit eas exit $ EL'Const nil
      Just !refKey ->
        el'ResolveContextAttr eas refKey >>= \case
          Nothing -> do
            el'LogDiag
              diags
              el'Warning
              addr'span
              "unknown-ref"
              "possible misspelled reference"
            recordAttrRef eac $ EL'UnsolvedRef Nothing addr'span
            returnAsExpr
          Just !attrDef -> do
            -- record as referencing symbol
            let !attrRef = EL'AttrRef Nothing addr mwip attrDef
            recordAttrRef eac attrRef

            el'Exit eas exit $ el'attr'def'value attrDef
    where
      !eac = el'context eas
      !mwip = el'ContextModule eac
      diags = el'ctx'diags eac
      returnAsExpr = el'Exit eas exit $ EL'Expr xsrc
--

-- that reference
el'AnalyzeExpr
  (ExprSrc (AttrExpr ThatRef {}) _expr'span)
  !exit
  !eas = el'Exit eas exit $ EL'ObjVal mwip thisObj
    where
      -- TODO such faking with this obj okay?

      !eac = el'context eas
      !mwip = el'ContextModule eac
      !thisObj = el'ContextObject eac
--

-- this reference
el'AnalyzeExpr
  (ExprSrc (AttrExpr ThisRef {}) _expr'span)
  !exit
  !eas = el'Exit eas exit $ EL'ObjVal mwip thisObj
    where
      !eac = el'context eas
      !mwip = el'ContextModule eac
      !thisObj = el'ContextObject eac
--

-- super reference
el'AnalyzeExpr
  (ExprSrc (AttrExpr SuperRef {}) _expr'span)
  !exit
  !eas = el'Exit eas exit $ EL'ObjVal mwip thisObj
    where
      -- TODO such faking with this obj okay?

      !eac = el'context eas
      !mwip = el'ContextModule eac
      !thisObj = el'ContextObject eac
--

-- indirect attribute addressing (dot-notation)
el'AnalyzeExpr
  xsrc@( ExprSrc
           ( AttrExpr
               ( IndirectRef
                   !tgtExpr
                   addr@(AttrAddrSrc _ !addr'span)
                 )
             )
           _expr'span
         )
  !exit
  !eas = el'RunTx eas $
    el'AnalyzeExpr tgtExpr $ \ !tgtVal _eas ->
      el'ResolveAttrAddr eas addr $ \case
        Nothing -> do
          recordAttrRef eac $ EL'UnsolvedRef (Just tgtVal) addr'span
          returnAsExpr
        Just !refKey -> case el'UltimateValue' mwip tgtVal of
          -- object instance attribute addressing
          (_valModu, srcVal@(EL'ObjVal !objModu !obj)) ->
            iopdLookup refKey (el'obj'attrs obj) >>= \case
              Nothing ->
                iopdLookup refKey (el'class'attrs $ el'obj'class obj) >>= \case
                  Nothing -> do
                    el'LogDiag
                      diags
                      el'Error
                      addr'span
                      "no-obj-attr"
                      "no such object attribute"
                    recordAttrRef eac $ EL'UnsolvedRef (Just srcVal) addr'span
                    returnAsExpr
                  Just !attrDef -> do
                    -- record as referencing symbol
                    let (!origModu, !origDef) = el'UltimateDefi objModu attrDef
                    recordAttrRef eac $
                      EL'AttrRef (Just srcVal) addr origModu origDef

                    el'Exit eas exit $ el'attr'def'value attrDef
              Just !attrDef -> do
                -- record as referencing symbol
                let (!origModu, !origDef) = el'UltimateDefi objModu attrDef
                recordAttrRef eac $
                  EL'AttrRef (Just srcVal) addr origModu origDef

                el'Exit eas exit $ el'attr'def'value attrDef
          --

          -- static class attribute addressing
          (_valModu, srcVal@(EL'ClsVal !clsModu !cls)) ->
            iopdLookup refKey (el'class'attrs cls) >>= \case
              Nothing -> case refKey of
                AttrByName "name" ->
                  -- TODO provide proper value
                  returnAsExpr
                AttrByName "mro" ->
                  -- TODO provide proper value
                  returnAsExpr
                _ -> do
                  el'LogDiag
                    diags
                    el'Error
                    addr'span
                    "no-cls-attr"
                    "no such class attribute"
                  recordAttrRef eac $ EL'UnsolvedRef (Just srcVal) addr'span
                  returnAsExpr
              Just !attrDef -> do
                -- record as referencing symbol
                let (!origModu, !origDef) = el'UltimateDefi clsModu attrDef
                recordAttrRef eac $
                  EL'AttrRef (Just srcVal) addr origModu origDef

                el'Exit eas exit $ el'attr'def'value attrDef
          --

          -- apk addressing
          ( _valModu,
            srcVal@(EL'Apk (EL'ArgsPack _args !kwargs _dyn'args !dyn'kwargs))
            ) ->
              case odLookup refKey kwargs of
                Nothing -> do
                  if dyn'kwargs
                    then
                      el'LogDiag
                        diags
                        el'Warning
                        addr'span
                        "dyn-apk-attr"
                        "dynamic named argument"
                    else
                      el'LogDiag
                        diags
                        el'Error
                        addr'span
                        "no-apk-attr"
                        "no such named argument"
                  recordAttrRef eac $ EL'UnsolvedRef (Just srcVal) addr'span
                  returnAsExpr
                Just !attrVal -> case attrVal of
                  EL'External !valModu !valDef -> do
                    -- record as referencing symbol
                    let (!origModu, !origDef) = el'UltimateDefi valModu valDef
                    recordAttrRef eac $
                      EL'AttrRef (Just srcVal) addr origModu origDef

                    el'Exit eas exit attrVal
                  _ -> do
                    -- TODO should apk.kwargs store definitions instead? so here
                    -- a reference can be recorded
                    recordAttrRef eac $ EL'UnsolvedRef (Just srcVal) addr'span
                    el'Exit eas exit attrVal
          --

          -- EL'ModuVal !ms -> undefined -- TODO handle this
          -- EL'ProcVal !p -> undefined -- TODO handle this
          -- EL'Const (EdhDict (Dict _ _ds)) -> undefined -- TODO handle this
          --

          -- unrecognized value
          (_valModu, !srcVal) -> do
            -- TODO handle these:
            --  * virtual properties
            --  * procedure arg with known type, such as `callerScope`
            --  * tgt with annotated type
            --
            -- then warn otherwise not resolvable
            el'LogDiag
              diags
              el'Warning
              addr'span
              "unknown-member"
              "possible misspelled member reference"
            --

            -- record as unsolved referencing symbol, or completion will list
            -- scope attrs within its range, unsolved ref leads to no completion
            -- item, which should be more desirable
            recordAttrRef eac $ EL'UnsolvedRef (Just srcVal) addr'span

            returnAsExpr
    where
      !eac = el'context eas
      !mwip = el'ContextModule eac
      diags = el'ctx'diags eac

      returnAsExpr = el'Exit eas exit $ EL'Expr xsrc
--

-- infix operator application
el'AnalyzeExpr
  xsrc@( ExprSrc
           ( InfixExpr
               (OpSymSrc !opSym (SrcRange op'start _op'end))
               lhExpr@(ExprSrc !lhx lh'span@(SrcRange _lh'start lh'end))
               !rhExpr
             )
           !expr'span
         )
  !exit
  !eas = case opSym of
    -- infix form of at-notation
    "@" -> do
      when
        ( src'line op'start > src'line lh'end
            || src'char op'start > src'char lh'end + 1
        )
        $ el'LogDiag
          diags
          el'Error
          (SrcRange lh'end op'start)
          "unintended-at-notation"
          "you want to put a semicolon here, or it is infix at-notation"
      el'RunTx eas $
        el'AnalyzeExpr lhExpr $
          const $ -- TODO validate attribute key available from lhs value
            el'AnalyzeExpr rhExpr $ const returnAsExpr

    -- comparisons
    "==" -> doCmp
    "!=" -> doCmp
    ">=" -> doCmp
    "<=" -> doCmp
    ">" -> doCmp
    "<" -> doCmp
    "is" -> doCmp
    "is not" -> doCmp
    "in" -> doCmp
    "is in" -> doCmp
    "not in" -> doCmp
    "is not in" -> doCmp
    --

    -- assignment
    _ | "=" `T.isSuffixOf` opSym -> doAssign
    --

    -- branch
    "->" -> doBranch
    --

    -- vanilla/generator arrow procedure
    "=>" ->
      el'RunTx eas $
        el'DefineArrowProc
          (methodArrowArgsReceiver . deParen'1)
          (AttrByName "<arrow>")
          lhExpr
          rhExpr
          exit
    --  producer arrow procedure
    "=>*" ->
      el'RunTx eas $
        el'DefineArrowProc
          (producerArrowArgsReceiver . deParen'1)
          (AttrByName "<producer>")
          lhExpr
          rhExpr
          exit
    --

    -- attribute prototype annotation
    "=:" -> doAssign
    --

    -- attribute type annotation
    "::" -> case lhExpr of
      ExprSrc (AttrExpr (DirectRef !addr)) _ ->
        el'ResolveAttrAddr eas addr $ \case
          Nothing -> returnAsExpr eas
          Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
          Just !attrKey -> do
            !attrAnno <- EL'AttrAnno rhExpr <$> readTVar (el'doc'cmt eas)
            iopdInsert attrKey attrAnno (el'branch'annos'wip bwip)
            el'Exit eas exit $ EL'Const nil
      ExprSrc (InfixExpr (OpSymSrc "@" _) _ _) _ ->
        -- very possibly to be annotation of bare at-notation,
        -- unintended to be parsed as infix at-notation,
        -- will be diag'ed by analyzing it
        el'RunTx eas $
          el'AnalyzeExpr lhExpr $ \_lhVal !eas' -> returnAsExpr eas'
      ExprSrc _ !bad'anno'span -> do
        el'LogDiag
          diags
          el'Warning
          bad'anno'span
          "bad-attr-anno"
          "bad attribute annotation"
        returnAsExpr eas
    --

    -- type synonym annotation
    ":=:" -> case lhExpr of
      ExprSrc (AttrExpr (DirectRef !addr)) _ ->
        el'ResolveAttrAddr eas addr $ \case
          Nothing -> returnAsExpr eas
          Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
          Just !attrKey -> do
            !attrAnno <- EL'AttrAnno rhExpr <$> readTVar (el'doc'cmt eas)
            -- TODO use separate fields
            iopdInsert attrKey attrAnno (el'branch'annos'wip bwip)
            el'Exit eas exit $ EL'Const nil
      ExprSrc _ !bad'anno'span -> do
        el'LogDiag
          diags
          el'Warning
          bad'anno'span
          "bad-type-anno"
          "bad type synonym annotation"
        returnAsExpr eas
    --

    -- free-form lhs annotation
    "!" -> el'RunTx eas $ el'AnalyzeExpr rhExpr exit
    --

    -- TODO special treatment of ($) (|) (&) etc. ?

    -- other operations without special treatment
    _ ->
      el'RunTx eas $
        el'AnalyzeExpr lhExpr $
          const $
            el'AnalyzeExpr rhExpr $ const returnAsExpr
            --

            --
    where
      !eac = el'context eas
      diags = el'ctx'diags eac
      !mwip = el'ContextModule eac
      !swip = el'ctx'scope eac
      !pwip = el'ProcWIP swip
      !bwip = el'scope'branch'wip pwip
      returnAsExpr = el'ExitTx exit $ EL'Expr xsrc

      doCmp :: STM ()
      doCmp =
        el'RunTx eas $
          el'AnalyzeExpr lhExpr $
            const $
              el'AnalyzeExpr rhExpr $ const returnAsExpr

      doAssign :: STM ()
      doAssign = do
        !docCmt <- takeDocComment eas
        el'RunTx eas $
          el'AnalyzeExpr rhExpr $ \ !rhVal !easDone -> do
            case lhExpr of
              ExprSrc
                ( AttrExpr
                    (DirectRef addr@(AttrAddrSrc _ !addr'span))
                  )
                _ ->
                  el'ResolveAttrAddr easDone addr $ \case
                    Nothing -> returnAsExpr easDone
                    Just (AttrByName "_") -> el'Exit easDone exit $ EL'Const nil
                    Just !attrKey -> do
                      !attrAnno <-
                        newTVar =<< iopdLookup attrKey (el'branch'annos'wip bwip)
                      !maybePrevDef <-
                        iopdLookup attrKey $
                          if el'ctx'eff'defining eac
                            then el'branch'effs'wip bwip
                            else el'branch'attrs'wip bwip
                      let !attrDef =
                            EL'AttrDef
                              attrKey
                              docCmt
                              opSym
                              addr'span
                              xsrc
                              rhVal
                              attrAnno
                              maybePrevDef

                      -- record as artifact of current scope
                      if el'ctx'eff'defining eac
                        then do
                          -- todo (+=) (*=) etc. are working but confusing for effect definition
                          --      log errors/warnings case by case, for ops other than (=) or (:=)
                          let !effs = el'branch'effs'wip bwip
                          case rhVal of
                            EL'Const EdhNil -> iopdDelete attrKey effs
                            _ -> iopdInsert attrKey attrDef effs
                          el'Exit easDone exit rhVal
                        else do
                          -- note the assignment defines attr regardless of pure ctx
                          let !attrs = el'branch'attrs'wip bwip
                          if el'IsNil rhVal && "=" == opSym
                            then do
                              iopdDelete attrKey $ el'scope'attrs'wip pwip
                              iopdDelete attrKey attrs
                              iopdSnapshot attrs
                                >>= modifyTVar' (el'branch'regions'wip bwip) . (:)
                                  . EL'Region (src'end expr'span)
                            else do
                              iopdInsert attrKey attrDef $ el'scope'attrs'wip pwip
                              iopdInsert attrKey attrDef attrs
                              case maybePrevDef of
                                -- assignment created a new attr, record a region
                                -- after this assignment expr for current scope
                                Nothing ->
                                  iopdSnapshot attrs
                                    >>= modifyTVar' (el'branch'regions'wip bwip)
                                      . (:)
                                      . EL'Region (src'end expr'span)
                                _ -> pure ()
                          when (el'ctx'exporting eac) $
                            iopdInsert attrKey attrDef $
                              el'obj'exps $ el'scope'this'obj pwip
                          --

                          -- note "?=" goes otherwise
                          if opSym `elem` ["=", ":=", "|=", "=:"]
                            then do
                              -- check if it shadows attr from outer scopes
                              case swip of
                                EL'InitObject {} -> pure () -- not eligible
                                EL'DefineClass {} -> pure () -- not eligible
                                EL'InitModule {} -> pure () -- need check?
                                EL'ProcFlow {} ->
                                  el'ResolveLexicalAttr (el'ctx'outers eac) attrKey
                                    >>= \case
                                      Nothing -> pure ()
                                      Just !shadowedDef -> do
                                        el'LogDiag
                                          diags
                                          el'Warning
                                          addr'span
                                          "attr-shadow"
                                          "shadows the attribute defined in outer scope"
                                        -- record a reference to the shadowed attr
                                        let !attrRef =
                                              EL'AttrRef Nothing addr mwip shadowedDef
                                        recordAttrRef eac attrRef

                              -- record as reference symbol, for completion
                              recordAttrRef eac $
                                EL'UnsolvedRef Nothing addr'span
                              -- record as definition symbol
                              recordAttrDef eac attrDef
                              el'Exit easDone exit rhVal
                            else case maybePrevDef of
                              Just !prevDef -> do
                                -- record as reference symbol
                                recordAttrRef eac $
                                  EL'AttrRef Nothing addr mwip prevDef
                                returnAsExpr easDone
                              Nothing -> do
                                -- record as definition symbol
                                recordAttrDef eac attrDef
                                returnAsExpr easDone
              ExprSrc
                ( AttrExpr
                    (IndirectRef !tgtExpr addr@(AttrAddrSrc _ !addr'span))
                  )
                _expr'span ->
                  el'RunTx easDone $
                    el'AnalyzeExpr tgtExpr $ \ !tgtVal !easDone' -> do
                      -- record as reference symbol, for completion
                      recordAttrRef eac $
                        EL'UnsolvedRef (Just tgtVal) addr'span
                      el'ResolveAttrAddr easDone' addr $ \case
                        Nothing ->
                          -- record as reference symbol, for completion
                          recordAttrRef eac $ EL'UnsolvedRef Nothing addr'span
                        Just !attrKey ->
                          case tgtVal of
                            EL'ObjVal _ms !obj -> do
                              let !cls = el'obj'class obj
                                  !objAttrs = el'obj'attrs obj
                              !maybePrevDef <- el'ResolveObjAttr obj attrKey
                              case maybePrevDef of
                                Just !prevDef ->
                                  -- record as reference symbol
                                  recordAttrRef eac $
                                    EL'AttrRef Nothing addr mwip prevDef
                                Nothing -> pure ()
                              !attrAnno <-
                                (newTVar =<<) $
                                  tryReadTMVar (el'class'defi cls) >>= \case
                                    Nothing -> return Nothing
                                    Just !defi ->
                                      return $
                                        odLookup attrKey $ el'class'annos defi
                              let !attrDef =
                                    EL'AttrDef
                                      attrKey
                                      docCmt
                                      opSym
                                      addr'span
                                      xsrc
                                      rhVal
                                      attrAnno
                                      maybePrevDef
                              iopdInsert attrKey attrDef objAttrs
                            -- TODO more to do?
                            _ -> pure ()
                      returnAsExpr easDone'
              ExprSrc (IndexExpr !idxExpr !tgtExpr) _expr'span ->
                el'RunTx easDone $
                  el'AnalyzeExpr idxExpr $
                    const $
                      el'AnalyzeExpr tgtExpr $ const returnAsExpr
              ExprSrc (InfixExpr (OpSymSrc "@" _) _ _) _ ->
                el'RunTx easDone $
                  el'AnalyzeExpr lhExpr $ -- assuming it be update, i.e.
                  -- initial assignment should not happen this way
                    \_lhVal !easDone' -> returnAsExpr easDone'
              ExprSrc _ !bad'assign'tgt'span -> do
                el'LogDiag
                  diags
                  el'Error
                  bad'assign'tgt'span
                  "bad-assign-target"
                  "bad assignment target"
                returnAsExpr easDone

      doBranch :: STM ()
      doBranch = do
        let (!fullExpr, !maybeGuardExpr) = case lhx of
              -- pattern or value match, guarded
              InfixExpr (OpSymSrc "|" _) (ExprSrc !matchExpr _) !guardExpr ->
                (matchExpr, Just guardExpr)
              -- pattern or value match
              _ -> (lhx, Nothing)

            defExprAttrs ::
              [(AttrKey, ExprSrc)] ->
              ( [(AttrKey, EL'AttrDef)] ->
                STM ()
              ) ->
              STM ()
            defExprAttrs !kes !daExit = go kes []
              where
                go :: [(AttrKey, ExprSrc)] -> [(AttrKey, EL'AttrDef)] -> STM ()
                go [] !kds = daExit kds
                go ((!attrKey, !attrExpr) : rest) !kds = do
                  !attrAnno <- newTVar Nothing
                  !maybePrevDef <-
                    iopdLookup attrKey $
                      if el'ctx'eff'defining eac
                        then el'branch'effs'wip bwip
                        else el'branch'attrs'wip bwip
                  let !attrDef =
                        EL'AttrDef
                          attrKey
                          NoDocCmt
                          opSym
                          (exprSrcSpan attrExpr)
                          xsrc
                          (EL'Expr attrExpr)
                          attrAnno
                          maybePrevDef
                  go rest ((attrKey, attrDef) : kds)

            defDfAttrs ::
              EL'ModuSlot ->
              EL'Class ->
              [ArgSender] ->
              ( [(AttrKey, EL'AttrDef)] ->
                STM ()
              ) ->
              STM ()
            defDfAttrs !clsModu !cls !sndrs !daExit = go sndrs []
              where
                go :: [ArgSender] -> [(AttrKey, EL'AttrDef)] -> STM ()
                go [] !kds = daExit kds
                go (sndr : rest) !kds = do
                  !attrAnno <- newTVar Nothing
                  case sndr of
                    SendPosArg
                      attrExpr@( ExprSrc
                                   (AttrExpr (DirectRef !rcvAttr))
                                   !arg'span
                                 ) ->
                        el'ResolveAttrAddr eas rcvAttr $ \case
                          Nothing -> go rest kds
                          Just !key -> do
                            !attrVal <-
                              el'ResolveObjAttr' cls key >>= \case
                                Nothing -> do
                                  el'LogDiag
                                    diags
                                    el'Error
                                    arg'span
                                    "missing-data-field"
                                    "no such data class field"
                                  return $ EL'Expr attrExpr
                                Just !def -> do
                                  recordAttrRef eac $
                                    EL'AttrRef Nothing rcvAttr clsModu def
                                  return $ el'attr'def'value def
                            let !attrDef =
                                  EL'AttrDef
                                    key
                                    NoDocCmt
                                    opSym
                                    arg'span
                                    xsrc
                                    attrVal
                                    attrAnno
                                    Nothing
                            go rest $ (key, attrDef) : kds
                    SendKwArg
                      srcAttr@(AttrAddrSrc _ !src'span)
                      attrExpr@( ExprSrc
                                   (AttrExpr (DirectRef !tgtAttr))
                                   !arg'span
                                 ) ->
                        el'ResolveAttrAddr eas srcAttr $ \case
                          Nothing -> go rest kds
                          Just !srcKey ->
                            el'ResolveAttrAddr eas tgtAttr $ \case
                              Nothing -> go rest kds
                              Just !tgtKey -> do
                                !attrVal <-
                                  el'ResolveObjAttr' cls srcKey >>= \case
                                    Nothing -> do
                                      el'LogDiag
                                        diags
                                        el'Error
                                        src'span
                                        "missing-data-field"
                                        "no such data class field"
                                      return $ EL'Expr attrExpr
                                    Just !def -> do
                                      recordAttrRef eac $
                                        EL'AttrRef Nothing srcAttr clsModu def
                                      return $ el'attr'def'value def
                                let !attrDef =
                                      EL'AttrDef
                                        tgtKey
                                        NoDocCmt
                                        opSym
                                        arg'span
                                        xsrc
                                        attrVal
                                        attrAnno
                                        Nothing
                                go rest $ (tgtKey, attrDef) : kds
                    _ -> do
                      el'LogDiag
                        diags
                        el'Error
                        (argSenderSpan sndr)
                        "bad-data-field"
                        "bad data class field extractor"
                      go rest kds

            defPosAttrs ::
              [ArgSender] ->
              ( [(AttrKey, EL'AttrDef)] ->
                STM ()
              ) ->
              STM ()
            defPosAttrs !sndrs !daExit = go sndrs []
              where
                go :: [ArgSender] -> [(AttrKey, EL'AttrDef)] -> STM ()
                go [] !kds = daExit kds
                go (sndr : rest) !kds = do
                  !attrAnno <- newTVar Nothing
                  case sndr of
                    SendPosArg
                      attrExpr@( ExprSrc
                                   (AttrExpr (DirectRef !rcvAttr))
                                   !arg'span
                                 ) ->
                        el'ResolveAttrAddr eas rcvAttr $ \case
                          Nothing -> go rest kds
                          Just !key -> do
                            let !attrDef =
                                  EL'AttrDef
                                    key
                                    NoDocCmt
                                    opSym
                                    arg'span
                                    xsrc
                                    (EL'Expr attrExpr)
                                    attrAnno
                                    Nothing
                            go rest $ (key, attrDef) : kds
                    _ -> do
                      el'LogDiag
                        diags
                        el'Error
                        (argSenderSpan sndr)
                        "bad-pos-match"
                        "bad positional match declaration"
                      go rest kds

            analyzeBranch :: [(AttrKey, EL'AttrDef)] -> STM ()
            analyzeBranch !ps = do
              !branchAttrs <- iopdClone $ el'branch'attrs'wip bwip
              iopdUpdate ps branchAttrs
              iopdUpdate ps $ el'scope'attrs'wip pwip
              !branchEffs <- iopdClone $ el'branch'effs'wip bwip
              !branchAnnos <- iopdClone $ el'branch'annos'wip bwip
              !branchRegions <- newTVar []
              let !bwipBranch =
                    bwip
                      { el'branch'attrs'wip = branchAttrs,
                        el'branch'effs'wip = branchEffs,
                        el'branch'annos'wip = branchAnnos,
                        el'branch'regions'wip = branchRegions
                      }
                  !eacBranch =
                    eac {el'ctx'scope = el'SwitchBranch bwipBranch swip}
                  !easBranch = eas {el'context = eacBranch}

                  analyzeContent =
                    el'AnalyzeExpr rhExpr $
                      -- XXX the branch fallthrough has bug, later artifacts
                      -- are not available during analyze of inner scopes
                      -- of previous scopes, need further investigation
                      \_rhResult _easDone -> do
                        -- \ !rhResult !easDone -> do
                        --   -- TODO fill annos of ps from branchAnnos now
                        --   case rhResult of
                        --     EL'Const EdhFallthrough -> do
                        --       -- this branch leaks to its following code
                        --       !prevRegions <-
                        --         readTVar
                        --           (el'branch'regions'wip bwip)
                        --       modifyTVar' branchRegions (++ prevRegions)
                        --       el'Exit easDone exit $ EL'Expr xsrc
                        --     _ -> do
                        -- this branch closes
                        !regions <- readTVar branchRegions
                        modifyTVar' (el'scope'regions'wip pwip) (regions ++)
                        el'Exit eas exit $ EL'Expr xsrc

              case maybeGuardExpr of
                Nothing -> el'RunTx easBranch analyzeContent
                Just !guardExpr ->
                  el'RunTx easBranch $
                    el'AnalyzeExpr guardExpr $ const analyzeContent

            invalidPattern :: STM ()
            invalidPattern = do
              el'LogDiag
                diags
                el'Error
                lh'span
                "invalid-pattern"
                "invalid match pattern"
              analyzeBranch []

            handlePairPattern ::
              [(AttrKey, EL'AttrDef)] ->
              ExprSrc ->
              STM ()
            handlePairPattern
              !defs
              p1Expr@(ExprSrc !p1x _) = case p1x of
                AttrExpr
                  ( DirectRef
                      (AttrAddrSrc (NamedAttr !p1Name) !p1Span)
                    ) -> do
                    !p1Anno <- newTVar Nothing
                    let !p1Key = AttrByName p1Name
                        !p1Def =
                          EL'AttrDef
                            p1Key
                            NoDocCmt
                            opSym
                            p1Span
                            xsrc
                            (EL'Expr p1Expr)
                            p1Anno
                            Nothing
                    analyzeBranch $! (p1Key, p1Def) : defs
                InfixExpr
                  (OpSymSrc ":" _)
                  !p2Expr
                  p1Expr'@( ExprSrc
                              ( AttrExpr
                                  ( DirectRef
                                      (AttrAddrSrc (NamedAttr !p1Name) !p1Span)
                                    )
                                )
                              _
                            ) -> do
                    !p1Anno <- newTVar Nothing
                    let !p1Key = AttrByName p1Name
                        !p1Def =
                          EL'AttrDef
                            p1Key
                            NoDocCmt
                            opSym
                            p1Span
                            xsrc
                            (EL'Expr p1Expr')
                            p1Anno
                            Nothing
                    handlePairPattern ((p1Key, p1Def) : defs) p2Expr
                _ -> invalidPattern

        case fullExpr of
          -- wild match
          AttrExpr (DirectRef (AttrAddrSrc (NamedAttr "_") _)) ->
            analyzeBranch []
          --

          -- curly braces at lhs means a pattern
          BlockExpr !patternExpr -> case patternExpr of
            -- { val } -- wild capture pattern
            [ StmtSrc
                ( ExprStmt
                    valExpr@(AttrExpr (DirectRef !valAddr))
                    _docCmt
                  )
                !stmt'span
              ] ->
                el'ResolveAttrAddr eas valAddr $ \case
                  Nothing -> analyzeBranch []
                  Just !attrKey ->
                    defExprAttrs
                      [(attrKey, ExprSrc valExpr stmt'span)]
                      analyzeBranch
            --

            -- { class( field1, field2, ... ) } -- fields by class pattern
            -- __match__ magic from the class works here
            [ StmtSrc
                ( ExprStmt
                    (CallExpr clsExpr@ExprSrc {} (ArgsPacker !apkr _))
                    _docCmt
                  )
                _
              ] -> el'RunTx eas $
                el'AnalyzeExpr clsExpr $
                  \ !clsResult _eas -> case el'UltimateValue clsResult of
                    EL'ClsVal !clsModu !cls ->
                      defDfAttrs clsModu cls apkr analyzeBranch
                    _ -> defDfAttrs mwip el'MetaClass apkr analyzeBranch
            -- { class( field1, field2, ... ) = instAddr } -- fields by
            -- class again, but receive the matched object as well
            -- __match__ magic from the class works here
            [ StmtSrc
                ( ExprStmt
                    ( InfixExpr
                        (OpSymSrc "=" _)
                        ( ExprSrc
                            ( CallExpr
                                clsExpr@ExprSrc {}
                                (ArgsPacker !apkr _)
                              )
                            _
                          )
                        instExpr@( ExprSrc
                                     (AttrExpr (DirectRef !instAddr))
                                     !inst'span
                                   )
                      )
                    _docCmt
                  )
                _
              ] -> el'RunTx eas $
                el'AnalyzeExpr clsExpr $
                  \ !clsResult _eas -> case el'UltimateValue clsResult of
                    EL'ClsVal !clsModu !cls -> do
                      !obj <- el'ObjNew cls
                      defDfAttrs clsModu cls apkr $ \ !dfs ->
                        el'ResolveAttrAddr eas instAddr $ \case
                          Nothing -> analyzeBranch dfs
                          Just !instKey -> do
                            !anno <- newTVar Nothing
                            let !attrDef =
                                  EL'AttrDef
                                    instKey
                                    NoDocCmt
                                    opSym
                                    inst'span
                                    instExpr
                                    (EL'ObjVal clsModu obj)
                                    anno
                                    Nothing
                            analyzeBranch $ dfs ++ [(instKey, attrDef)]
                    _ -> defDfAttrs mwip el'MetaClass apkr $ \ !dfs ->
                      el'ResolveAttrAddr eas instAddr $ \case
                        Nothing -> analyzeBranch dfs
                        Just !instKey -> do
                          !anno <- newTVar Nothing
                          let !attrDef =
                                EL'AttrDef
                                  instKey
                                  NoDocCmt
                                  opSym
                                  inst'span
                                  instExpr
                                  (EL'Expr instExpr)
                                  anno
                                  Nothing
                          analyzeBranch $ dfs ++ [(instKey, attrDef)]
            -- {{ class:inst }} -- instance resolving pattern
            [ StmtSrc
                ( ExprStmt
                    ( DictExpr
                        [ ( AddrDictKey clsAddr@(AttrAddrSrc _ !cls'span),
                            instExpr@( ExprSrc
                                         ( AttrExpr
                                             ( DirectRef
                                                 instAddr@( AttrAddrSrc
                                                              _
                                                              !inst'span
                                                            )
                                               )
                                           )
                                         _
                                       )
                            )
                          ]
                      )
                    _docCmt
                  )
                _
              ] ->
                el'ResolveAttrAddr eas instAddr $ \case
                  Nothing -> analyzeBranch []
                  Just !instKey -> el'RunTx eas $
                    el'AnalyzeExpr
                      (ExprSrc (AttrExpr (DirectRef clsAddr)) cls'span)
                      $ \ !clsResult _eas -> case el'UltimateValue clsResult of
                        EL'ClsVal !clsModu !cls -> do
                          !obj <- el'ObjNew cls
                          !anno <- newTVar Nothing
                          let !attrDef =
                                EL'AttrDef
                                  instKey
                                  NoDocCmt
                                  opSym
                                  inst'span
                                  instExpr
                                  (EL'ObjVal clsModu obj)
                                  anno
                                  Nothing
                          analyzeBranch [(instKey, attrDef)]
                        _ -> do
                          !anno <- newTVar Nothing
                          let !attrDef =
                                EL'AttrDef
                                  instKey
                                  NoDocCmt
                                  opSym
                                  inst'span
                                  instExpr
                                  (EL'Expr instExpr)
                                  anno
                                  Nothing
                          analyzeBranch [(instKey, attrDef)]
            --

            -- {[ x,y,z,... ]} -- any-of pattern
            [StmtSrc (ExprStmt (ListExpr !vExprs) _docCmt) _] ->
              el'RunTx eas $ -- todo: chain of eas is broken here,
              -- for blocks / branches to reside in the elements,
              -- we'd better keep the chain
                el'AnalyzeExprs vExprs $ \_result _eas -> analyzeBranch []
            --

            -- { head :> tail } -- uncons pattern
            [ StmtSrc
                ( ExprStmt
                    ( InfixExpr
                        (OpSymSrc ":>" _)
                        headExpr@( ExprSrc
                                     ( AttrExpr
                                         ( DirectRef
                                             ( AttrAddrSrc
                                                 (NamedAttr !headName)
                                                 _
                                               )
                                           )
                                       )
                                     _
                                   )
                        tailExpr@( ExprSrc
                                     ( AttrExpr
                                         ( DirectRef
                                             ( AttrAddrSrc
                                                 (NamedAttr !tailName)
                                                 _
                                               )
                                           )
                                       )
                                     _
                                   )
                      )
                    _docCmt
                  )
                _
              ] ->
                defExprAttrs
                  [ (AttrByName headName, headExpr),
                    (AttrByName tailName, tailExpr)
                  ]
                  analyzeBranch
            --

            -- { prefix @< match >@ suffix } -- sub-string cut pattern
            [ StmtSrc
                ( ExprStmt
                    ( InfixExpr
                        (OpSymSrc ">@" _)
                        prefixExpr@( ExprSrc
                                       ( InfixExpr
                                           (OpSymSrc "@<" _)
                                           ( ExprSrc
                                               ( AttrExpr
                                                   ( DirectRef
                                                       ( AttrAddrSrc
                                                           ( NamedAttr
                                                               !prefixName
                                                             )
                                                           _
                                                         )
                                                     )
                                                 )
                                               _
                                             )
                                           !matchExpr
                                         )
                                       _
                                     )
                        suffixExpr@( ExprSrc
                                       ( AttrExpr
                                           ( DirectRef
                                               ( AttrAddrSrc
                                                   (NamedAttr !suffixName)
                                                   _
                                                 )
                                             )
                                         )
                                       _
                                     )
                      )
                    _docCmt
                  )
                _
              ] -> el'RunTx eas $
                el'AnalyzeExpr matchExpr $ \_result _eas ->
                  defExprAttrs
                    [ (AttrByName prefixName, prefixExpr),
                      (AttrByName suffixName, suffixExpr)
                    ]
                    analyzeBranch
            -- { match >@ suffix } -- prefix cut pattern
            [ StmtSrc
                ( ExprStmt
                    ( InfixExpr
                        (OpSymSrc ">@" _)
                        !prefixExpr
                        suffixExpr@( ExprSrc
                                       ( AttrExpr
                                           ( DirectRef
                                               ( AttrAddrSrc
                                                   (NamedAttr !suffixName)
                                                   _
                                                 )
                                             )
                                         )
                                       _
                                     )
                      )
                    _docCmt
                  )
                _
              ] -> el'RunTx eas $
                el'AnalyzeExpr prefixExpr $ \_result _eas ->
                  defExprAttrs
                    [(AttrByName suffixName, suffixExpr)]
                    analyzeBranch
            -- { prefix @< match } -- suffix cut pattern
            [ StmtSrc
                ( ExprStmt
                    ( InfixExpr
                        (OpSymSrc "@<" _)
                        prefixExpr@( ExprSrc
                                       ( AttrExpr
                                           ( DirectRef
                                               ( AttrAddrSrc
                                                   (NamedAttr !prefixName)
                                                   _
                                                 )
                                             )
                                         )
                                       _
                                     )
                        !suffixExpr
                      )
                    _docCmt
                  )
                _
              ] -> el'RunTx eas $
                el'AnalyzeExpr suffixExpr $ \_result _eas ->
                  defExprAttrs
                    [(AttrByName prefixName, prefixExpr)]
                    analyzeBranch
            --

            -- {( x )} -- single arg
            [ StmtSrc
                ( ExprStmt
                    ( ParenExpr
                        argExpr@( ExprSrc
                                    ( AttrExpr
                                        ( DirectRef
                                            ( AttrAddrSrc
                                                (NamedAttr !attrName)
                                                _
                                              )
                                          )
                                      )
                                    _
                                  )
                      )
                    _docCmt
                  )
                _
              ] -> do
                let !attrKey = AttrByName attrName
                defExprAttrs [(attrKey, argExpr)] analyzeBranch
            -- {( x,y,z,... )} -- pattern matching number of positional args
            [ StmtSrc
                (ExprStmt (ArgsPackExpr (ArgsPacker !argSenders _)) _docCmt)
                _
              ] -> defPosAttrs argSenders analyzeBranch
            --

            -- {( x:y:z:... )} -- pair pattern
            [ StmtSrc
                ( ExprStmt
                    ( ParenExpr
                        p1Expr@(ExprSrc (InfixExpr (OpSymSrc ":" _) _ _) _)
                      )
                    _docCmt
                  )
                _
              ] -> handlePairPattern [] p1Expr
            --

            -- { continue } -- match with continue
            [StmtSrc ContinueStmt _] -> analyzeBranch []
            -- { break } -- match with break
            [StmtSrc BreakStmt _] -> analyzeBranch []
            -- { fallthrough } -- match with fallthrough
            [StmtSrc FallthroughStmt _] -> analyzeBranch []
            -- { return <attr> } -- capture return value
            [ StmtSrc
                ( ReturnStmt
                    valExpr@( ExprSrc
                                ( AttrExpr
                                    ( DirectRef
                                        ( AttrAddrSrc
                                            (NamedAttr !valueName)
                                            val'span
                                          )
                                      )
                                  )
                                _
                              )
                    _docCmt
                  )
                _
              ] -> do
                !anno <- newTVar Nothing
                let !valKey = AttrByName valueName
                    !attrDef =
                      EL'AttrDef
                        valKey
                        NoDocCmt
                        opSym
                        val'span
                        valExpr
                        (EL'Expr valExpr)
                        anno
                        Nothing
                analyzeBranch [(valKey, attrDef)]
            -- { return <expr> } -- match with expected return value
            [StmtSrc (ReturnStmt _expectExpr _docCmt) _] -> analyzeBranch []
            --

            -- { term := value } -- definition pattern
            [ StmtSrc
                ( ExprStmt
                    ( InfixExpr
                        (OpSymSrc ":=" _)
                        termExpr@( ExprSrc
                                     ( AttrExpr
                                         ( DirectRef
                                             ( AttrAddrSrc
                                                 (NamedAttr !termName)
                                                 _
                                               )
                                           )
                                       )
                                     _
                                   )
                        valueExpr@( ExprSrc
                                      ( AttrExpr
                                          ( DirectRef
                                              ( AttrAddrSrc
                                                  (NamedAttr !valueName)
                                                  _
                                                )
                                            )
                                        )
                                      _
                                    )
                      )
                    _docCmt
                  )
                _
              ] ->
                defExprAttrs
                  [ (AttrByName termName, termExpr),
                    (AttrByName valueName, valueExpr)
                  ]
                  analyzeBranch
            --

            -- TODO more patterns to support
            _ -> invalidPattern
          --

          -- guarded condition branch
          PrefixExpr Guard !condExpr -> el'RunTx eas $
            el'AnalyzeExpr condExpr $
              \_cndResult _eas -> analyzeBranch []
          --

          -- this is to establish the intuition that `{ ... }` always
          -- invokes pattern matching.
          -- TODO hint that if a literal dict value really meant to be
          -- matched, the parenthesized form `( {k1: v1, k2: v2, ...} )`
          -- should be used.
          DictExpr {} -> invalidPattern
          --

          -- not a pattern, value match
          _ -> el'RunTx eas $
            el'AnalyzeExpr lhExpr $
              \_lhResult _eas -> analyzeBranch []
--

-- apk ctor
el'AnalyzeExpr (ExprSrc (ArgsPackExpr !argSndrs) _expr'span) !exit !eas =
  el'RunTx eas $ el'PackArgs argSndrs $ \ !apk -> el'ExitTx exit $ EL'Apk apk
--

-- list ctor
el'AnalyzeExpr (ExprSrc (ListExpr !xs) _) !exit !eas = el'RunTx eas $
  el'AnalyzeExprs xs $ \ !vs !easDone ->
    el'Exit easDone exit . EL'List =<< newTVar vs
--

-- dict ctor
el'AnalyzeExpr (ExprSrc (DictExpr !es) _) !exit !eas =
  el'RunTx easPure $ collectEntries [] es
  where
    !eac = el'context eas
    !easPure = eas {el'context = eac {el'ctx'pure = True}}
    !originPure = el'ctx'pure eac

    collectEntries ::
      [(EL'Value, EL'Value)] ->
      [(DictKeyExpr, ExprSrc)] ->
      EL'Tx
    collectEntries !evs [] = \ !easDone ->
      el'Exit
        easDone {el'context = (el'context easDone) {el'ctx'pure = originPure}}
        exit
        . EL'Dict
        =<< (newTVar $! reverse evs)
    collectEntries !evs ((!dkx, !vx) : rest) =
      el'AnalyzeExpr vx $ \ !v -> case dkx of
        LitDictKey !lit -> \ !easDone ->
          el'LiteralValue lit >>= \ !k ->
            el'RunTx easDone $ collectEntries ((k, v) : evs) rest
        AddrDictKey !kaddr -> el'AnalyzeExpr
          (ExprSrc (AttrExpr (DirectRef kaddr)) noSrcRange)
          $ \ !k -> collectEntries ((k, v) : evs) rest
        ExprDictKey !kx -> el'AnalyzeExpr kx $ \ !k ->
          collectEntries ((k, v) : evs) rest
--

-- parenthesis
el'AnalyzeExpr (ExprSrc (ParenExpr !x) _) !exit !eas =
  el'RunTx easPure $
    el'AnalyzeExpr x $ \ !val !easDone ->
      el'Exit
        easDone
          { el'context = (el'context easDone) {el'ctx'pure = originPure}
          }
        exit
        val
  where
    !eac = el'context eas
    !easPure = eas {el'context = eac {el'ctx'pure = True}}
    !originPure = el'ctx'pure eac
--

-- literal value
el'AnalyzeExpr (ExprSrc (LitExpr !lit) _expr'span) !exit !eas =
  el'Exit eas exit =<< el'LiteralValue lit
--

-- call making
el'AnalyzeExpr
  xsrc@(ExprSrc (CallExpr !calleeExpr !apkr) _expr'span)
  !exit
  !eas = do
    when
      ( paren'start'line > callee'end'line
          || paren'start'char > callee'end'char + 1
      )
      $ el'LogDiag
        diags
        el'Error
        (SrcRange callee'end paren'start)
        "unintended-call"
        "you want to put a semicolon here, or it is procedure call making"

    el'RunTx eas $
      el'AnalyzeExpr calleeExpr $ \ !calleeVal -> el'PackArgs apkr $
        \_apk !easDone -> case el'UltimateValue calleeVal of
          EL'ClsVal !clsModu !cls -> do
            !obj <- el'ObjNew cls
            el'Exit easDone exit $ EL'ObjVal clsModu obj
          _ ->
            -- TODO honor procedure annotation for return type, thus reified
            -- value to return from here
            el'Exit easDone exit $ EL'Expr xsrc
    where
      !eac = el'context eas
      diags = el'ctx'diags eac
      SrcRange _ callee'end@(SrcPos !callee'end'line !callee'end'char) =
        exprSrcSpan calleeExpr
      ArgsPacker
        _
        ( SrcRange
            paren'start@( SrcPos
                            !paren'start'line
                            !paren'start'char
                          )
            _
          ) = apkr
--

-- exporting
el'AnalyzeExpr (ExprSrc (ExportExpr !expr') _expr'span) !exit !eas =
  el'RunTx eas {el'context = eac {el'ctx'exporting = True}} $
    el'AnalyzeExpr expr' exit
  where
    !eac = el'context eas
--

-- including
el'AnalyzeExpr
  xsrc@(ExprSrc (IncludeExpr incSpec@(ExprSrc !specExpr !spec'span)) _)
  !exit
  !eas = case specExpr of
    LitExpr (StringLiteral !litSpec) -> case el'ContextModule' eac of
      Nothing -> do
        el'LogDiag
          diags
          el'Error
          spec'span
          "moduleless-include"
          "include from non-module context"
        el'Exit eas exit $ EL'Const nil
      Just (!msImporter, !resolvImporter) ->
        el'RunTx eas $
          el'LocateIncludee msImporter litSpec $ \ !incResult _eas ->
            case incResult of
              Left !err -> do
                el'LogDiag diags el'Error spec'span "err-include" err
                el'Exit eas exit $ EL'Const nil
              Right !msImportee -> do
                -- record a reference to the src module
                let !moduVal = EL'ModuVal msImportee
                    !incSrcDef =
                      EL'AttrDef
                        (AttrByName "this")
                        NoDocCmt
                        "<fragment>"
                        zeroSrcRange
                        ( ExprSrc
                            (AttrExpr (ThisRef noSrcRange))
                            noSrcRange
                        )
                        moduVal
                        maoAnnotation
                        Nothing
                    !incDef =
                      EL'AttrDef
                        (AttrByName litSpec)
                        NoDocCmt
                        "<include>"
                        noSrcRange
                        xsrc
                        (EL'External msImportee incSrcDef)
                        maoAnnotation
                        Nothing
                    !incRef =
                      EL'AttrRef
                        Nothing
                        (AttrAddrSrc (QuaintAttr litSpec) spec'span)
                        msImportee
                        incDef
                recordAttrRef eac incRef

                -- record as a dependency
                modifyTVar' (el'modu'dependencies'wip resolvImporter) $
                  Map.insert msImportee True
                -- do including whether it is resolving or resolved
                runEdhTx ets $
                  asModuleResolving world msImportee $ \case
                    EL'ModuResolved !resolved -> \_ets -> do
                      -- record includer as a dependant
                      modifyTVar' (el'modu'dependants resolved) $
                        Map.insert msImporter True
                      el'Exit eas exit moduVal
                    EL'ModuResolving !resolving _acts -> \_ets -> do
                      -- record includer as a dependant
                      modifyTVar' (el'resolving'dependants resolving) $
                        Map.insert msImporter True
                      el'Exit eas exit moduVal
    _ -> do
      el'LogDiag
        diags
        el'Warning
        spec'span
        "dynamic-include"
        "els does not analyze source structure of dynamic include yet"
      el'RunTx eas $ -- dynamic string include
      -- TODO analyzetime string eval?
        el'AnalyzeExpr incSpec $ \ !impFromVal -> do
          -- TODO validate it is string type, include from it
          el'ExitTx exit impFromVal
    where
      !world = el'world eas
      !ets = el'ets eas
      !eac = el'context eas
      diags = el'ctx'diags eac
--

-- importing
el'AnalyzeExpr
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
      Just _intoExpr -> do
        -- TODO resolve and use the target object
        --      note nil target should be allowed as nop
        !fakeScope <- iopdEmpty
        doImp fakeScope fakeScope
      Nothing -> doImp localScope localExps
    where
      !world = el'world eas
      !ets = el'ets eas
      !eac = el'context eas
      !swip = el'ctx'scope eac
      !pwip = el'ProcWIP swip
      !bwip = el'scope'branch'wip pwip
      diags = el'ctx'diags eac

      !localScope =
        if el'ctx'eff'defining eac
          then el'branch'effs'wip bwip
          else el'branch'attrs'wip bwip
      !localExps = el'obj'exps $ el'scope'this'obj pwip

      doImp :: EL'ArtsWIP -> EL'ArtsWIP -> STM ()
      doImp !intoScope !withExps = do
        !docCmt <- takeDocComment eas
        let chkExport :: STM (AttrKey -> EL'AttrDef -> STM ())
            chkExport =
              if not (el'ctx'exporting eac)
                then return $ \_ _ -> return ()
                else return $ \ !localKey !attrDef ->
                  iopdInsert localKey attrDef withExps

            impIntoScope ::
              (AttrKey -> EL'AttrDef -> STM ()) ->
              EL'ModuSlot ->
              EL'Artifacts ->
              ArgsReceiver ->
              STM ()
            impIntoScope !chkExp !srcModu !srcExps !asr = do
              case asr of
                WildReceiver _ -> forM_ (odToList srcExps) wildImp
                PackReceiver !ars _ -> go srcExps ars
                SingleReceiver !ar -> go srcExps [ar]
                NullaryReceiver -> go srcExps []
              -- record a region after this import, for current scope
              iopdSnapshot (el'branch'attrs'wip bwip)
                >>= modifyTVar' (el'branch'regions'wip bwip) . (:)
                  . EL'Region (src'end expr'span)
              where
                wildImp :: (AttrKey, EL'AttrDef) -> STM ()
                wildImp (!k, !def) = do
                  !artAnno <- newTVar =<< el'ResolveAnnotation swip k
                  let !attrDef =
                        EL'AttrDef
                          k
                          docCmt
                          "<import>"
                          expr'span
                          xsrc
                          (EL'External srcModu def)
                          artAnno
                          Nothing
                  iopdInsert k attrDef intoScope
                  chkExp k attrDef

                go :: OrderedDict AttrKey EL'AttrDef -> [ArgReceiver] -> STM ()
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
                  RecvRestPkArgs (AttrAddrSrc (NamedAttr "_") _) -> pure ()
                  RecvRestKwArgs (AttrAddrSrc (NamedAttr "_") _) -> pure ()
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
                  RecvRestPkArgs localAddr@(AttrAddrSrc _ !addr'span) ->
                    el'ResolveAttrAddr eas localAddr $ \case
                      Nothing ->
                        -- invalid attr addr, error should have been logged
                        go srcArts rest
                      Just (AttrByName "_") -> go odEmpty rest -- explicit dropping
                      Just !localKey -> do
                        !artAnno <- newTVar =<< el'ResolveAnnotation swip localKey
                        let !kwVal =
                              EL'Apk $
                                EL'ArgsPack
                                  []
                                  (odMap (EL'External srcModu) srcArts)
                                  False
                                  True
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
                        -- record as definition symbol
                        recordAttrDef eac attrDef

                        -- register as local attribute
                        iopdInsert localKey attrDef intoScope
                        -- export it if specified so
                        chkExp localKey attrDef

                        go odEmpty rest
                  RecvRestKwArgs localAddr@(AttrAddrSrc _ !addr'span) ->
                    el'ResolveAttrAddr eas localAddr $ \case
                      Nothing ->
                        -- invalid attr addr, error should have been logged
                        go srcArts rest
                      Just (AttrByName "_") -> go odEmpty rest -- explicit dropping
                      Just !localKey -> do
                        !artAnno <- newTVar =<< el'ResolveAnnotation swip localKey
                        let !kwVal =
                              EL'Apk $
                                EL'ArgsPack
                                  []
                                  (odMap (EL'External srcModu) srcArts)
                                  False
                                  True
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
                        -- record as definition symbol
                        recordAttrDef eac attrDef

                        -- register as local attribute
                        iopdInsert localKey attrDef intoScope
                        -- export it if specified so
                        chkExp localKey attrDef

                        go odEmpty rest
                  where
                    processImp :: AttrAddrSrc -> AttrAddrSrc -> STM ()
                    processImp
                      srcAddr@(AttrAddrSrc _ !src'span)
                      localAddr@(AttrAddrSrc _ !local'span) = do
                        el'ResolveAttrAddr eas localAddr $ \case
                          Nothing ->
                            -- invalid attr addr, error should have been logged
                            go srcArts rest
                          Just !localKey ->
                            el'ResolveAttrAddr eas srcAddr $ \case
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
                                      Just !srcDef -> do
                                        !artAnno <-
                                          newTVar
                                            =<< el'ResolveAnnotation swip localKey
                                        let !impDef =
                                              EL'AttrDef
                                                localKey
                                                docCmt
                                                "<import>"
                                                local'span
                                                xsrc
                                                (EL'External srcModu srcDef)
                                                artAnno
                                                Nothing
                                        -- record as definition symbol
                                        recordAttrDef eac impDef
                                        -- record as referencing symbol
                                        recordAttrRef eac $
                                          EL'AttrRef
                                            Nothing
                                            localAddr
                                            srcModu
                                            srcDef

                                        -- register as local attribute
                                        iopdInsert localKey impDef intoScope
                                        -- export it if specified so
                                        chkExp localKey impDef

                                        go srcArts' rest
        case specExpr of
          LitExpr (StringLiteral !litSpec) -> case el'ContextModule' eac of
            Nothing -> do
              el'LogDiag
                diags
                el'Error
                spec'span
                "moduleless-import"
                "import from non-module context"
              el'Exit eas exit $ EL'Const nil
            Just (!msImporter, !resolvImporter) ->
              el'RunTx eas $
                el'LocateImportee msImporter litSpec $ \ !impResult _eas ->
                  case impResult of
                    Left !err -> do
                      el'LogDiag diags el'Error spec'span "err-import" err
                      el'Exit eas exit $ EL'Const nil
                    Right !msImportee -> do
                      -- record a reference to the src module
                      let !moduVal = EL'ModuVal msImportee
                          !importeeDef =
                            EL'AttrDef
                              (AttrByName "this")
                              NoDocCmt
                              "<module>"
                              zeroSrcRange
                              ( ExprSrc
                                  (AttrExpr (ThisRef noSrcRange))
                                  noSrcRange
                              )
                              moduVal
                              maoAnnotation
                              Nothing
                          !impDef =
                            EL'AttrDef
                              (AttrByName litSpec)
                              docCmt
                              "<import>"
                              noSrcRange
                              xsrc
                              (EL'External msImportee importeeDef)
                              maoAnnotation
                              Nothing
                          !impRef =
                            EL'AttrRef
                              Nothing
                              (AttrAddrSrc (QuaintAttr litSpec) spec'span)
                              msImportee
                              impDef
                      recordAttrRef eac impRef

                      -- record as a dependency
                      modifyTVar' (el'modu'dependencies'wip resolvImporter) $
                        Map.insert msImportee True
                      -- do importing whether it is resolving or resolved
                      !chkExp <- chkExport
                      runEdhTx ets $
                        asModuleResolving world msImportee $ \case
                          EL'ModuResolved !resolved -> \_ets -> do
                            -- record importer as a dependant
                            modifyTVar' (el'modu'dependants resolved) $
                              Map.insert msImporter True
                            -- do import
                            let !exps = el'modu'exports resolved
                            impIntoScope chkExp msImportee exps argsRcvr
                            el'Exit eas exit moduVal
                          EL'ModuResolving !resolving _acts -> \_ets -> do
                            -- record importer as a dependant
                            modifyTVar' (el'resolving'dependants resolving) $
                              Map.insert msImporter True
                            -- do import
                            !exps <- iopdSnapshot $ el'modu'exps'wip resolving
                            impIntoScope chkExp msImportee exps argsRcvr
                            el'Exit eas exit moduVal
          _ -> do
            el'LogDiag
              diags
              el'Warning
              spec'span
              "dynamic-import"
              "els does not analyze source structure of dynamic import yet"
            el'RunTx eas $ -- dynamic string or obj import
            -- TODO analyzetime string/object eval?
              el'AnalyzeExpr impSpec $ \ !impFromVal -> do
                -- TODO validate it is object type, import from it
                el'ExitTx exit impFromVal
--

-- defining a class
el'AnalyzeExpr (ExprSrc (ClassExpr HostDecl {}) _expr'span) _exit _eas =
  error "bug: host class decl"
el'AnalyzeExpr
  xsrc@( ExprSrc
           ( ClassExpr
               ( ProcDecl
                   cls'name@(AttrAddrSrc _cls'name'addr !cls'name'span)
                   !argsRcvr
                   cls'body@(StmtSrc _body'stmt !body'span)
                   _cls'proc'loc
                 )
             )
           !expr'span
         )
  !exit
  !eas = el'ResolveAttrAddr eas cls'name $ \ !maybeClsKey -> do
    !docCmt <- takeDocComment eas
    !clsDefi <- newEmptyTMVar
    !clsAttrs <- iopdEmpty
    !clsExts <- newTVar []
    !clsExps <- iopdEmpty
    !instAttrs <- iopdEmpty
    !instExts <- newTVar []
    !instExps <- iopdEmpty
    let !clsObj = EL'Object el'MetaClass clsAttrs clsExts clsExps
        !cls =
          EL'Class
            (fromMaybe (AttrByName "<bad-class-name>") maybeClsKey)
            el'MetaClass
            clsDefi
            clsAttrs
            clsExts
            clsExps
            instAttrs
            instExts
            instExps
        !clsStub = EL'Object cls instAttrs instExts instExps

    !branchAttrs <- iopdEmpty
    !clsEffs <- iopdEmpty
    !clsAnnos <- iopdEmpty
    !branchRegions <- newTVar []
    !clsScopes <- newTVar []
    !clsRegions <- newTVar []
    let !bwip =
          EL'BranchWIP
            branchAttrs
            clsEffs
            clsAnnos
            branchRegions
        !pwip =
          EL'ProcWIP
            bwip
            clsAttrs
            clsObj
            clsScopes
            clsRegions
        !eacCls =
          EL'Context
            { el'ctx'scope =
                EL'DefineClass (EL'ClassWIP clsObj clsStub) pwip,
              el'ctx'outers = outerScope : el'ctx'outers eac,
              el'ctx'pure = False,
              el'ctx'exporting = False,
              el'ctx'eff'defining = False,
              el'ctx'attr'defs = el'ctx'attr'defs eac,
              el'ctx'attr'refs = el'ctx'attr'refs eac,
              el'ctx'diags = el'ctx'diags eac
            }
        !easCls = eas {el'context = eacCls}

        -- define artifacts from arguments (i.e. data fields) for a data
        -- class
        defDataArts :: [ArgReceiver] -> ([(AttrKey, EL'AttrDef)] -> STM ()) -> STM ()
        defDataArts !ars = go [] ars
          where
            go ::
              [(AttrKey, EL'AttrDef)] ->
              [ArgReceiver] ->
              ([(AttrKey, EL'AttrDef)] -> STM ()) ->
              STM ()
            go !dfs [] !exit' = exit' $ reverse dfs
            go !dfs (ar : rest) exit' = case ar of
              RecvArg
                dfAddr@(AttrAddrSrc _ df'span)
                !maybeRename
                _maybeDef ->
                  case maybeRename of
                    Nothing -> defDataField dfAddr exit'
                    Just (DirectRef !dfAddr') -> defDataField dfAddr' exit'
                    Just _badRename -> do
                      el'LogDiag
                        diags
                        el'Error
                        df'span
                        "bad-data-field-rename"
                        "bad data field rename"
                      go dfs rest exit'
              RecvRestPkArgs !dfAddr -> defDataField dfAddr exit'
              RecvRestKwArgs !dfAddr -> defDataField dfAddr exit'
              RecvRestPosArgs !dfAddr -> defDataField dfAddr exit'
              where
                defDataField (AttrAddrSrc (NamedAttr "_") _) !exit'' =
                  go dfs rest exit''
                defDataField dfAddr@(AttrAddrSrc _ df'name'span) !exit'' =
                  el'ResolveAttrAddr eas dfAddr $ \case
                    Nothing -> go dfs rest exit''
                    Just !dfKey -> do
                      -- TODO clsAnnos is empty now, fill the var later
                      !dfAnno <- newTVar =<< iopdLookup dfKey clsAnnos
                      go
                        ( ( dfKey,
                            EL'AttrDef
                              dfKey
                              NoDocCmt
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
                        exit''

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
                (DocCmt [mthDoc])
                "<data-class-def>"
                cls'name'span
                xsrc
                ( EL'ProcVal
                    mwip
                    ( EL'Proc
                        (AttrByName mthName)
                        NullaryReceiver -- todo elaborate actual args
                    )
                )
                anno
                Nothing
            )

    -- define data fields as instance attributes
    case argsRcvr of
      -- a data class (ADT)
      SingleReceiver !ar -> defDataArts [ar] $ flip iopdUpdate instAttrs
      PackReceiver !ars _ -> defDataArts ars $ flip iopdUpdate instAttrs
      WildReceiver !rcvr'span ->
        el'LogDiag
          diags
          el'Error
          rcvr'span
          "wild-data-fields"
          "wild data fields (reciver) for data class not supported"
      -- a normal class
      NullaryReceiver -> pure ()

    el'RunTx easCls $
      el'AnalyzeStmts [cls'body] $ \_ !easDone -> do
        let !eacDone = el'context easDone
            !swipDone = el'ctx'scope eacDone
            !pwipDone = el'ProcWIP swipDone
            !bwipDone = el'scope'branch'wip pwipDone
        !regions'wip <- readTVar (el'branch'regions'wip bwipDone)
        !innerScopes <- readTVar clsScopes
        !regions <-
          (regions'wip ++)
            <$> readTVar (el'scope'regions'wip pwipDone)

        let !cls'scope =
              EL'Scope
                { el'scope'span = body'span,
                  el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                  el'scope'regions = V.fromList $! reverse regions
                }
        -- record as an inner scope of outer scope
        modifyTVar' (el'scope'inner'scopes'wip outerProc) (cls'scope :)

        case maybeClsKey of
          Nothing -> el'Exit eas exit $ EL'Const nil
          Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
          Just !clsName -> do
            !cls'annos <- iopdSnapshot clsAnnos
            !clsAnno <- newTVar =<< el'ResolveAnnotation outerScope clsName
            let !mro = [] -- TODO C3 linearize cls'exts to get this
                !defi = EL'ClassDefi mro cls'scope cls'annos
                !clsVal = EL'ClsVal mwip cls
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
            putTMVar clsDefi defi
            -- record as definition symbol of outer scope
            recordAttrDef eac clsDef
            --

            -- record as artifact of outer scope
            unless (el'ctx'pure eac) $ do
              if el'ctx'eff'defining eac
                then iopdInsert clsName clsDef $ el'branch'effs'wip outerBranch
                else do
                  let !attrs = el'branch'attrs'wip outerBranch
                  iopdInsert clsName clsDef $ el'scope'attrs'wip outerProc
                  iopdInsert clsName clsDef attrs
                  -- record a region after this definition for current scope
                  iopdSnapshot attrs
                    >>= modifyTVar' (el'branch'regions'wip outerBranch) . (:)
                      . EL'Region (src'end expr'span)

              when (el'ctx'exporting eac) $
                iopdInsert clsName clsDef $
                  el'obj'exps $ el'scope'this'obj outerProc

            -- return the class object value
            el'Exit eas exit clsVal
    where
      !eac = el'context eas
      !mwip = el'ContextModule eac
      !outerScope = el'ctx'scope eac
      !outerProc = el'ProcWIP outerScope
      !outerBranch = el'scope'branch'wip outerProc
      diags = el'ctx'diags eac
--

-- defining a method procedure
el'AnalyzeExpr xsrc@(ExprSrc (MethodExpr !pd) _expr'span) !exit !eas =
  el'RunTx eas $ el'DefineMethod xsrc pd exit
el'AnalyzeExpr xsrc@(ExprSrc (GeneratorExpr !pd) _expr'span) !exit !eas =
  el'RunTx eas $ el'DefineMethod xsrc pd exit
el'AnalyzeExpr xsrc@(ExprSrc (InterpreterExpr !pd) _expr'span) !exit !eas =
  el'RunTx eas $ el'DefineMethod xsrc pd exit
el'AnalyzeExpr xsrc@(ExprSrc (ProducerExpr !pd) _expr'span) !exit !eas =
  el'RunTx eas $ el'DefineMethod xsrc pd exit
-- defining an operator procedure
el'AnalyzeExpr
  xsrc@( ExprSrc
           (OpDefiExpr _fixity _precedence _opSym !pd)
           _expr'span
         )
  !exit
  !eas =
    el'RunTx eas $ el'DefineMethod xsrc pd exit
el'AnalyzeExpr
  xsrc@( ExprSrc
           (OpOvrdExpr _fixity _precedence _opSym !pd)
           _expr'span
         )
  !exit
  !eas =
    el'RunTx eas $ el'DefineMethod xsrc pd exit
--

-- defining a namespace
el'AnalyzeExpr (ExprSrc (NamespaceExpr HostDecl {} _) _) _exit _eas =
  error "bug: host ns decl"
el'AnalyzeExpr
  xsrc@( ExprSrc
           ( NamespaceExpr
               ( ProcDecl
                   ns'name@(AttrAddrSrc _ns'name'addr !ns'name'span)
                   _
                   ns'body@(StmtSrc _body'stmt !body'span)
                   _ns'proc'loc
                 )
               (ArgsPacker !argsPkr _)
             )
           !expr'span
         )
  !exit
  !eas = do
    !docCmt <- takeDocComment eas
    defNsArgs argsPkr $ \ !argArts -> do
      !nsExts <- newTVar []
      !nsExps <- iopdEmpty
      !branchAttrs <- iopdFromList argArts
      !nsAttrs <- iopdFromList argArts
      !nsEffs <- iopdEmpty
      !nsAnnos <- iopdEmpty
      !branchRegions <- newTVar []
      !nsScopes <- newTVar []
      !nsRegions <- newTVar []
      let !nsObj = EL'Object el'NamespaceClass nsAttrs nsExts nsExps
          !bwip =
            EL'BranchWIP
              branchAttrs
              nsEffs
              nsAnnos
              branchRegions
          !pwip =
            EL'ProcWIP
              bwip
              nsAttrs
              nsObj
              nsScopes
              nsRegions
          !eacNs =
            EL'Context
              { el'ctx'scope =
                  EL'InitObject nsObj pwip,
                el'ctx'outers = outerScope : el'ctx'outers eac,
                el'ctx'pure = False,
                el'ctx'exporting = False,
                el'ctx'eff'defining = False,
                el'ctx'attr'defs = el'ctx'attr'defs eac,
                el'ctx'attr'refs = el'ctx'attr'refs eac,
                el'ctx'diags = el'ctx'diags eac
              }
          !easNs = eas {el'context = eacNs}

      -- record a region starting from beginning of the body
      iopdSnapshot nsAttrs
        >>= modifyTVar' branchRegions . (:)
          . EL'Region (src'start body'span)

      el'RunTx easNs $
        el'AnalyzeStmts [ns'body] $ \_ !easDone -> do
          let !eacDone = el'context easDone
              !swipDone = el'ctx'scope eacDone
              !pwipDone = el'ProcWIP swipDone
              !bwipDone = el'scope'branch'wip pwipDone
          !regions'wip <- readTVar (el'branch'regions'wip bwipDone)

          -- update annotations for arguments from body
          forM_ argArts $ \(!argName, !argDef) ->
            iopdLookup argName nsAnnos >>= \case
              Nothing -> pure ()
              Just !anno ->
                writeTVar (el'attr'def'anno argDef) $ Just anno
          --

          !innerScopes <- readTVar nsScopes
          !regions <-
            (regions'wip ++)
              <$> readTVar (el'scope'regions'wip pwipDone)
          let !ns'scope =
                EL'Scope
                  { el'scope'span = body'span,
                    el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                    el'scope'regions = V.fromList $! reverse regions
                  }
          -- record as an inner scope of outer scope
          modifyTVar' (el'scope'inner'scopes'wip outerProc) (ns'scope :)

          el'ResolveAttrAddr eas ns'name $ \case
            Nothing -> el'Exit eas exit $ EL'Const nil
            Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
            Just !nsName -> do
              !nsDefi <- newTMVar $ EL'ClassDefi [] ns'scope odEmpty
              !nsAnno <- newTVar =<< el'ResolveAnnotation outerScope nsName
              let !nsVal =
                    EL'ObjVal
                      mwip
                      nsObj
                        { el'obj'class =
                            el'NamespaceClass
                              { el'class'name = nsName,
                                el'class'defi = nsDefi
                              }
                        }
                  !nsDef =
                    EL'AttrDef
                      nsName
                      docCmt
                      "<namespace-def>"
                      ns'name'span
                      xsrc
                      nsVal
                      nsAnno
                      Nothing
              -- record as definition symbol of outer scope
              recordAttrDef eac nsDef
              --

              -- record as artifact of outer scope
              unless (el'ctx'pure eac) $ do
                if el'ctx'eff'defining eac
                  then iopdInsert nsName nsDef $ el'branch'effs'wip outerBranch
                  else do
                    let !attrs = el'branch'attrs'wip outerBranch
                    iopdInsert nsName nsDef $ el'scope'attrs'wip outerProc
                    iopdInsert nsName nsDef attrs
                    -- record a region after this definition for current scope
                    iopdSnapshot attrs
                      >>= modifyTVar' (el'branch'regions'wip outerBranch)
                        . (:)
                        . EL'Region (src'end expr'span)

                when (el'ctx'exporting eac) $
                  iopdInsert nsName nsDef $
                    el'obj'exps $ el'scope'this'obj outerProc

              -- return the namespace object value
              el'Exit eas exit nsVal
    where
      !eac = el'context eas
      !mwip = el'ContextModule eac
      !outerScope = el'ctx'scope eac
      !outerProc = el'ProcWIP outerScope
      !outerBranch = el'scope'branch'wip outerProc
      diags = el'ctx'diags eac

      -- define artifacts from arguments for a namespace
      defNsArgs ::
        [ArgSender] -> ([(AttrKey, EL'AttrDef)] -> STM ()) -> STM ()
      defNsArgs !aps !nsaExit = go [] aps
        where
          go :: [(AttrKey, EL'AttrDef)] -> [ArgSender] -> STM ()
          go !argArts [] = nsaExit $ reverse argArts
          go !argArts (argSndr : rest) = case argSndr of
            SendKwArg argAddr@(AttrAddrSrc _ !arg'name'span) !argExpr ->
              el'ResolveAttrAddr eas argAddr $ \case
                Nothing -> go argArts rest
                Just !argKey -> el'RunTx eas $
                  el'AnalyzeExpr argExpr $ \ !argVal _eas -> do
                    !argAnno <- newTVar Nothing
                    go
                      ( ( argKey,
                          EL'AttrDef
                            argKey
                            NoDocCmt
                            "<namespace-arg>"
                            arg'name'span
                            xsrc
                            argVal
                            argAnno
                            Nothing
                        ) :
                        argArts
                      )
                      rest
            UnpackKwArgs _kwExpr@(ExprSrc _ !argx'span) -> do
              el'LogDiag
                diags
                el'Warning
                argx'span
                "ns-unpack-kwargs"
                "not analyzed yet: unpacking kwargs to a namespace"
              go argArts rest
            SendPosArg (ExprSrc _ !argx'span) -> do
              el'LogDiag
                diags
                el'Error
                argx'span
                "invalid-ns-arg"
                "sending positional arg to a namespace"
              go argArts rest
            UnpackPosArgs (ExprSrc _ !argx'span) -> do
              el'LogDiag
                diags
                el'Error
                argx'span
                "invalid-ns-arg"
                "unpacking positional args to a namespace"
              go argArts rest
            UnpackPkArgs (ExprSrc _ !argx'span) -> do
              el'LogDiag
                diags
                el'Error
                argx'span
                "invalid-ns-arg"
                "unpacking apk to a namespace"
              go argArts rest
--

-- scoped block
el'AnalyzeExpr (ExprSrc (ScopedBlockExpr !stmts) !blk'span) !exit !eas =
  do
    !blkAttrs <- iopdEmpty
    !blkEffs <- iopdEmpty
    !blkAnnos <- iopdEmpty
    !branchRegions <- newTVar []
    !blkScopes <- newTVar []
    !blkRegions <- newTVar []
    let !bwip =
          outerBranch
            { el'branch'attrs'wip = blkAttrs,
              el'branch'effs'wip = blkEffs,
              el'branch'annos'wip = blkAnnos,
              el'branch'regions'wip = branchRegions
            }
        !pwip =
          outerProc -- inherit exts/exps from outer scope
            { el'scope'branch'wip = bwip,
              el'scope'attrs'wip = blkAttrs,
              el'scope'inner'scopes'wip = blkScopes,
              el'scope'regions'wip = blkRegions
            }
        !eacBlk =
          eac
            { el'ctx'scope = EL'ProcFlow pwip,
              el'ctx'outers = outerScope : el'ctx'outers eac
            }
        !easBlk = eas {el'context = eacBlk}

    el'RunTx easBlk $
      el'AnalyzeStmts stmts $ \ !resultVal !easDone -> do
        let !eacDone = el'context easDone
            !swipDone = el'ctx'scope eacDone
            !pwipDone = el'ProcWIP swipDone
            !bwipDone = el'scope'branch'wip pwipDone
        !regions'wip <- readTVar (el'branch'regions'wip bwipDone)
        !innerScopes <- readTVar blkScopes
        !regions <-
          (regions'wip ++)
            <$> readTVar (el'scope'regions'wip pwipDone)
        let !blk'scope =
              EL'Scope
                { el'scope'span = blk'span,
                  el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                  el'scope'regions = V.fromList $! reverse regions
                }
        --

        -- record as an inner scope of outer scope
        modifyTVar' (el'scope'inner'scopes'wip outerProc) (blk'scope :)

        -- return the result value
        el'Exit eas exit resultVal
  where
    !eac = el'context eas
    !outerScope = el'ctx'scope eac
    !outerProc = el'ProcWIP outerScope
    !outerBranch = el'scope'branch'wip outerProc
--

-- void operator
el'AnalyzeExpr (ExprSrc (VoidExpr !expr) _expr'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr expr $ const $ el'ExitTx exit $ EL'Const nil
--

-- ai operator
el'AnalyzeExpr (ExprSrc (AtoIsoExpr !expr) _expr'span) !exit !eas =
  el'RunTx eas $ el'AnalyzeExpr expr exit
--

-- prefix operator
el'AnalyzeExpr x@(ExprSrc (PrefixExpr _ !expr) _expr'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr expr $ const $ el'ExitTx exit $ EL'Expr x
--

-- if
el'AnalyzeExpr
  x@(ExprSrc (IfExpr !cond !cseq !maybeAlt) _expr'span)
  !exit
  !eas =
    -- TODO use branch in cseq/alt, close when it evals to `return`
    el'RunTx eas $
      el'AnalyzeExpr cond $
        const $
          el'AnalyzeStmt cseq $
            const $ case maybeAlt of
              Nothing -> el'ExitTx exit $ EL'Expr x
              Just !alt ->
                el'AnalyzeStmt alt $ const $ el'ExitTx exit $ EL'Expr x
--

-- case-of
el'AnalyzeExpr x@(ExprSrc (CaseExpr !tgt !bs) !expr'span) !exit !eas0 =
  el'RunTx eas0 $
    el'AnalyzeExpr tgt $
      const $
        el'AnalyzeExpr bs $ \_result !eas -> do
          let !eac = el'context eas
              !swip = el'ctx'scope eac
              !pwip = el'ProcWIP swip
              !bwip = el'scope'branch'wip pwip
              !scope'attrs = el'scope'attrs'wip pwip
              !branch'attrs = el'branch'attrs'wip bwip
          !bas <- iopdSize branch'attrs
          -- merge all scope attrs into branch attrs
          flip iopdUpdate branch'attrs =<< iopdToList scope'attrs
          !bas' <- iopdSize branch'attrs
          when (bas' /= bas) $ do
            -- record a new region following this case-of as attrs changed
            !attrs <- iopdSnapshot branch'attrs
            modifyTVar'
              (el'branch'regions'wip bwip)
              (EL'Region (src'end expr'span) attrs :)

          el'Exit eas exit $ EL'Expr x
--

-- for-from-do loop
el'AnalyzeExpr
  x@(ExprSrc (ForExpr !scoped !asr !it body@(StmtSrc _ !body'span)) _expr'span)
  !exit
  !eas = do
    !eacLoop <-
      if not scoped
        then return eac
        else do
          !loopAttrs <- iopdEmpty
          !loopEffs <- iopdEmpty
          !loopAnnos <- iopdEmpty
          !branchRegions <- newTVar []
          !loopScopes <- newTVar []
          !loopRegions <- newTVar []
          let !bwip =
                looperBranch
                  { el'branch'attrs'wip = loopAttrs,
                    el'branch'effs'wip = loopEffs,
                    el'branch'annos'wip = loopAnnos,
                    el'branch'regions'wip = branchRegions
                  }
              !pwip =
                looperProc -- inherit exts/exps from looper scope
                  { el'scope'branch'wip = bwip,
                    el'scope'attrs'wip = loopAttrs,
                    el'scope'inner'scopes'wip = loopScopes,
                    el'scope'regions'wip = loopRegions
                  }
              !eacLoop =
                eac
                  { el'ctx'scope = EL'ProcFlow pwip,
                    el'ctx'outers = looperScope : el'ctx'outers eac
                  }
          return eacLoop

    let !easLoop = eas {el'context = eacLoop}
        !swip = el'ctx'scope eacLoop
        !pwip = el'ProcWIP swip
        !bwip = el'scope'branch'wip pwip
        !attrs = el'branch'attrs'wip bwip
        !annos = el'branch'annos'wip bwip

        -- define artifacts from loop receivers
        defLoopArts ::
          [ArgReceiver] -> ([(AttrKey, EL'AttrDef)] -> STM ()) -> STM ()
        defLoopArts !ars = go [] ars
          where
            go ::
              [(AttrKey, EL'AttrDef)] ->
              [ArgReceiver] ->
              ([(AttrKey, EL'AttrDef)] -> STM ()) ->
              STM ()
            go !args [] !exit' = exit' $ reverse args
            go !args (ar : rest) !exit' = case ar of
              RecvArg !argAddr !maybeRename !maybeDef -> case maybeRename of
                Nothing -> defLoopArt argAddr maybeDef exit'
                Just (DirectRef !argAddr') -> defLoopArt argAddr' Nothing exit'
                Just _otherRename -> go args rest exit' -- TODO elaborate?
              RecvRestPkArgs !argAddr -> defLoopArt argAddr Nothing exit'
              RecvRestKwArgs !argAddr -> defLoopArt argAddr Nothing exit'
              RecvRestPosArgs !argAddr -> defLoopArt argAddr Nothing exit'
              where
                defLoopArt (AttrAddrSrc (NamedAttr "_") _) _ !exit'' =
                  go args rest exit''
                defLoopArt
                  argAddr@(AttrAddrSrc _ arg'name'span)
                  !knownExpr
                  !exit'' =
                    el'ResolveAttrAddr easLoop argAddr $ \case
                      Nothing -> go args rest exit''
                      Just !argKey ->
                        iopdLookup argKey annos >>= newTVar >>= \ !anno ->
                          go
                            ( ( argKey,
                                EL'AttrDef
                                  argKey
                                  NoDocCmt
                                  "<loop-receiver>"
                                  arg'name'span
                                  x
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
                            exit''

    ( case asr of
        PackReceiver !ars _ -> defLoopArts ars
        SingleReceiver !ar -> defLoopArts [ar]
        WildReceiver _ -> ($ [])
        NullaryReceiver -> ($ [])
      )
      $ \ !loopArts -> do
        unless (null loopArts) $ do
          iopdUpdate loopArts $ el'scope'attrs'wip pwip
          iopdUpdate loopArts attrs
          -- record a region before the loop body for current scope
          iopdSnapshot attrs
            >>= modifyTVar' (el'branch'regions'wip bwip) . (:)
              . EL'Region (src'start body'span)

        el'RunTx eas $
          el'AnalyzeExpr it $ \_ _eas -> el'RunTx easLoop $
            el'AnalyzeStmt body $ \_result _eas -> do
              -- record a new region following this for-from-do loop
              -- TODO check whether new attrs actually added, don't record if not
              !scope'attrs <- iopdSnapshot (el'scope'attrs'wip pwip)
              modifyTVar'
                (el'branch'regions'wip bwip)
                (EL'Region (src'end body'span) scope'attrs :)

              el'Exit eas exit $ EL'Expr x
    where
      !eac = el'context eas
      looperScope = el'ctx'scope eac
      looperProc = el'ProcWIP looperScope
      looperBranch = el'scope'branch'wip looperProc

--

-- while
el'AnalyzeExpr (ExprSrc (WhileExpr !expr !body) _expr'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr expr $
      const $ el'AnalyzeStmt body $ const $ el'ExitTx exit $ EL'Const nil
--

-- do while
el'AnalyzeExpr (ExprSrc (DoWhileExpr !body !expr) _expr'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeStmt body $
      const $ el'AnalyzeExpr expr $ const $ el'ExitTx exit $ EL'Const nil
--

-- yield
el'AnalyzeExpr x@(ExprSrc (YieldExpr !expr) _expr'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr expr $ const $ el'ExitTx exit $ EL'Expr x
--

-- indexing
el'AnalyzeExpr x@(ExprSrc (IndexExpr !idx !tgt) _expr'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr tgt $
      const $ el'AnalyzeExpr idx $ const $ el'ExitTx exit $ EL'Expr x
--

-- default
el'AnalyzeExpr
  x@(ExprSrc (DefaultExpr Nothing !expr) _expr'span)
  !exit
  !eas =
    el'RunTx eas $
      el'AnalyzeExpr expr $ const $ el'ExitTx exit $ EL'Expr x
el'AnalyzeExpr
  x@(ExprSrc (DefaultExpr (Just !argSndrs) !expr) _expr'span)
  !exit
  !eas =
    el'RunTx eas $
      el'PackArgs argSndrs $ \_apk ->
        el'AnalyzeExpr expr $ const $ el'ExitTx exit $ EL'Expr x
--

-- interpolated expr
-- todo should this reachable ? as the original expr in ExprWithSrc won't be
-- analyzed.
el'AnalyzeExpr (ExprSrc (IntplExpr !expr) _expr'span) !exit !eas =
  el'RunTx eas $ el'AnalyzeExpr expr exit
--

-- expr with source (including interpolations)
el'AnalyzeExpr
  (ExprSrc (ExprWithSrc !expr !segs) _expr'span)
  !exit
  !eas = go segs
    where
      go [] = el'Exit eas exit $ EL'Expr expr
      go (SrcSeg {} : rest) = go rest
      go (IntplSeg !ix : rest) = el'RunTx eas $
        el'AnalyzeExpr ix $ \_ _eas -> go rest
--

-- effect callouts
-- todo analyze dynamic scoped effects
el'AnalyzeExpr x@(ExprSrc (EffExpr _effAddr) _expr'span) !exit !eas =
  el'Exit eas exit $ EL'Expr x
--

-- symbol definition
el'AnalyzeExpr xsrc@(ExprSrc (SymbolExpr !attr) !expr'span) !exit !eas =
  do
    !docCmt <- takeDocComment eas
    !sym <- mkSymbol $ "@" <> attr
    !symAnno <-
      newTVar
        =<< iopdLookup
          (AttrByName attr)
          (el'branch'annos'wip bwip)
    let !symVal = EL'Const $ EdhSymbol sym
        !symDef =
          EL'AttrDef
            symName
            docCmt
            "<sym-def>"
            expr'span
            xsrc
            symVal
            symAnno
            Nothing

    -- record as definition symbol
    recordAttrDef eac symDef

    -- record as artifact of current scope
    unless (el'ctx'pure eac) $ do
      let !attrs = el'branch'attrs'wip bwip
      iopdInsert symName symDef $ el'scope'attrs'wip pwip
      iopdInsert symName symDef attrs
      -- record a region after this definition for current scope
      iopdSnapshot attrs
        >>= modifyTVar' (el'branch'regions'wip bwip) . (:)
          . EL'Region (src'end expr'span)

      when (el'ctx'exporting eac) $
        iopdInsert symName symDef $ el'obj'exps $ el'scope'this'obj pwip

    -- return the symbol value
    el'Exit eas exit symVal
  where
    !eac = el'context eas
    !swip = el'ctx'scope eac
    !pwip = el'ProcWIP swip
    !bwip = el'scope'branch'wip pwip

    !symName = AttrByName attr

--

-- the rest of expressions not analyzed
-- el'AnalyzeExpr  !xsrc !exit !eas = el'Exit eas exit $ EL'Expr xsrc

-- | define a method procedure
el'DefineMethod ::
  ExprSrc ->
  ProcDecl ->
  EL'Analysis EL'Value
el'DefineMethod _ HostDecl {} _exit _eas =
  error "bug: host method decl"
el'DefineMethod
  !xsrc
  ( ProcDecl
      mth'name@(AttrAddrSrc _mth'name'addr !mth'name'span)
      !argsRcvr
      mth'body@(StmtSrc _body'stmt !body'span)
      _mth'proc'loc
    )
  !exit
  !eas = el'ResolveAttrAddr eas mth'name $ \ !maybeMthName -> do
    !docCmt <- takeDocComment eas
    let !mthPhase = case maybeMthName of
          Just (AttrByName "__init__") -> DefinePhase
          -- TODO other cases ?
          _ -> CallInPhase
    el'ScheduleAnalysis (el'ana'queue eas) mthPhase analyzeMthCall

    -- define the attribute & return the value at level of current scope
    case maybeMthName of
      Nothing -> el'Exit eas exit $ EL'Const nil
      Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
      Just !mthName -> do
        !mthAnno <- newTVar =<< el'ResolveAnnotation outerScope mthName
        let !mth = EL'Proc mthName argsRcvr
            !mthVal = EL'ProcVal mwip mth
            !mthDef =
              EL'AttrDef
                mthName
                docCmt
                "<proc-def>"
                mth'name'span
                xsrc
                mthVal
                mthAnno
                Nothing
        -- record as definition symbol of outer scope
        recordAttrDef eac mthDef
        --

        -- record as artifact of outer scope
        unless (el'ctx'pure eac) $ do
          if el'ctx'eff'defining eac
            then iopdInsert mthName mthDef $ el'branch'effs'wip outerBranch
            else do
              let !attrs = el'branch'attrs'wip outerBranch
              iopdInsert mthName mthDef $ el'scope'attrs'wip outerProc
              iopdInsert mthName mthDef attrs
              -- record a region after this definition for current scope
              iopdSnapshot attrs
                >>= modifyTVar' (el'branch'regions'wip outerBranch) . (:)
                  . EL'Region (src'end body'span)

          when (el'ctx'exporting eac) $
            iopdInsert mthName mthDef $
              el'obj'exps $ el'scope'this'obj outerProc

        -- return the procedure value
        el'Exit eas exit mthVal
    where
      !eac = el'context eas
      !mwip = el'ContextModule eac
      !outerScope = el'ctx'scope eac
      !outerProc = el'ProcWIP outerScope
      !outerBranch = el'scope'branch'wip outerProc
      -- diags = el'ctx'diags eac

      analyzeMthCall :: STM () -> STM ()
      analyzeMthCall !doneMthCall = do
        !mthAttrs <- iopdEmpty
        !mthEffs <- iopdEmpty
        !mthAnnos <- iopdEmpty
        !branchRegions <- newTVar []
        !mthScopes <- newTVar []
        !mthRegions <- newTVar []
        let !bwip =
              outerBranch
                { el'branch'attrs'wip = mthAttrs,
                  el'branch'effs'wip = mthEffs,
                  el'branch'annos'wip = mthAnnos,
                  el'branch'regions'wip = branchRegions
                }
            !pwip = case outerScope of
              EL'DefineClass !cwip _pwip ->
                outerProc
                  { el'scope'branch'wip = bwip,
                    el'scope'this'obj = el'class'stub'wip cwip,
                    el'scope'inner'scopes'wip = mthScopes,
                    el'scope'regions'wip = mthRegions
                  }
              _ ->
                outerProc -- inherit exts/exps from outer scope
                  { el'scope'branch'wip = bwip,
                    el'scope'inner'scopes'wip = mthScopes,
                    el'scope'regions'wip = mthRegions
                  }
            !eacMth =
              EL'Context
                { el'ctx'scope = EL'ProcFlow pwip,
                  el'ctx'outers = outerScope : el'ctx'outers eac,
                  el'ctx'pure = False,
                  el'ctx'exporting = False,
                  el'ctx'eff'defining = False,
                  el'ctx'attr'defs = el'ctx'attr'defs eac,
                  el'ctx'attr'refs = el'ctx'attr'refs eac,
                  el'ctx'diags = el'ctx'diags eac
                }
            !easMth = eas {el'context = eacMth}

        ( case argsRcvr of
            PackReceiver !ars _ -> defArgArts easMth "<method-arg>" xsrc ars
            SingleReceiver !ar -> defArgArts easMth "<method-arg>" xsrc [ar]
            WildReceiver _ -> ($ [])
            NullaryReceiver -> ($ [])
          )
          $ \ !argArts -> do
            iopdUpdate argArts mthAttrs

            el'RunTx easMth $
              el'AnalyzeStmts [mth'body] $ \_ !easDone -> do
                let !eacDone = el'context easDone
                    !swipDone = el'ctx'scope eacDone
                    !pwipDone = el'ProcWIP swipDone
                    !bwipDone = el'scope'branch'wip pwipDone
                !regions'wip <- readTVar (el'branch'regions'wip bwipDone)
                !innerScopes <- readTVar mthScopes
                !regions <-
                  (regions'wip ++)
                    <$> readTVar (el'scope'regions'wip pwipDone)

                -- update annotations for arguments from body
                forM_ argArts $ \(!argName, !argDef) ->
                  iopdLookup argName mthAnnos >>= \case
                    Nothing -> pure ()
                    Just !anno -> writeTVar (el'attr'def'anno argDef) $ Just anno
                --

                let !mth'scope =
                      EL'Scope
                        { el'scope'span = body'span,
                          el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                          el'scope'regions = V.fromList $! reverse regions
                        }
                -- record as an inner scope of outer scope
                modifyTVar' (el'scope'inner'scopes'wip outerProc) (mth'scope :)

                -- done analyzing this method call
                doneMthCall

--

-- | define an arrow procedure
el'DefineArrowProc ::
  (Expr -> (Either Text ArgsReceiver -> STM ()) -> STM ()) ->
  AttrKey ->
  ExprSrc ->
  ExprSrc ->
  EL'Analysis EL'Value
el'DefineArrowProc
  !argsRcvrCnvrt
  !mthName
  lhExpr@(ExprSrc !argPkr !args'span)
  rhExpr@(ExprSrc _ !body'span)
  !exit
  !eas =
    argsRcvrCnvrt argPkr $ \case
      Left !argErr -> do
        el'LogDiag diags el'Error args'span "bad-arrow-args" argErr
        withArgsRcvr (PackReceiver [] noSrcRange)
      Right !argsRcvr -> withArgsRcvr argsRcvr
    where
      !eac = el'context eas
      !mwip = el'ContextModule eac
      !outerScope = el'ctx'scope eac
      !outerProc = el'ProcWIP outerScope
      !outerBranch = el'scope'branch'wip outerProc
      diags = el'ctx'diags eac

      withArgsRcvr :: ArgsReceiver -> STM ()
      withArgsRcvr !argsRcvr = do
        el'ScheduleAnalysis (el'ana'queue eas) CallInPhase (analyzeMthCall argsRcvr)

        -- return the procedure value
        el'Exit eas exit $ EL'ProcVal mwip $ EL'Proc mthName argsRcvr

      analyzeMthCall :: ArgsReceiver -> STM () -> STM ()
      analyzeMthCall !argsRcvr !doneMthCall = do
        !mthAttrs <- iopdEmpty
        !mthEffs <- iopdEmpty
        !mthAnnos <- iopdEmpty
        !mthScopes <- newTVar []
        !mthRegions <- newTVar []
        let !bwip =
              outerBranch
                { el'branch'attrs'wip = mthAttrs,
                  el'branch'effs'wip = mthEffs,
                  el'branch'annos'wip = mthAnnos
                }
            !pwip = case outerScope of
              EL'DefineClass !cwip _pwip ->
                outerProc
                  { el'scope'branch'wip = bwip,
                    el'scope'this'obj = el'class'stub'wip cwip,
                    el'scope'inner'scopes'wip = mthScopes,
                    el'scope'regions'wip = mthRegions
                  }
              _ ->
                outerProc -- inherit exts/exps from outer scope
                  { el'scope'branch'wip = bwip,
                    el'scope'inner'scopes'wip = mthScopes,
                    el'scope'regions'wip = mthRegions
                  }
            !eacMth =
              EL'Context
                { el'ctx'scope = EL'ProcFlow pwip,
                  el'ctx'outers = outerScope : el'ctx'outers eac,
                  el'ctx'pure = False,
                  el'ctx'exporting = False,
                  el'ctx'eff'defining = False,
                  el'ctx'attr'defs = el'ctx'attr'defs eac,
                  el'ctx'attr'refs = el'ctx'attr'refs eac,
                  el'ctx'diags = el'ctx'diags eac
                }
            !easMth = eas {el'context = eacMth}

        ( case argsRcvr of
            PackReceiver !ars _ -> defArgArts easMth "<arrow-arg>" lhExpr ars
            SingleReceiver !ar -> defArgArts easMth "<arrow-arg>" lhExpr [ar]
            WildReceiver _ -> ($ [])
            NullaryReceiver -> ($ [])
          )
          $ \ !argArts -> do
            iopdUpdate argArts mthAttrs

            el'RunTx easMth $
              el'AnalyzeExpr rhExpr $ \_ !easDone -> do
                let !eacDone = el'context easDone
                    !swipDone = el'ctx'scope eacDone
                    !pwipDone = el'ProcWIP swipDone
                    !bwipDone = el'scope'branch'wip pwipDone
                !regions'wip <- readTVar (el'branch'regions'wip bwipDone)
                !innerScopes <- readTVar mthScopes
                !regions <-
                  (regions'wip ++)
                    <$> readTVar (el'scope'regions'wip pwipDone)

                -- update annotations for arguments from body
                forM_ argArts $ \(!argName, !argDef) ->
                  iopdLookup argName mthAnnos >>= \case
                    Nothing -> pure ()
                    Just !anno -> writeTVar (el'attr'def'anno argDef) $ Just anno
                --

                let !mth'scope =
                      EL'Scope
                        { el'scope'span = body'span,
                          el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                          el'scope'regions = V.fromList $! reverse regions
                        }
                --

                -- record as an inner scope of outer scope
                modifyTVar' (el'scope'inner'scopes'wip outerProc) (mth'scope :)

                -- done analyzing this method call
                doneMthCall

--

-- define artifacts from arguments for a procedure
defArgArts ::
  EL'AnalysisState ->
  OpSymbol ->
  ExprSrc ->
  [ArgReceiver] ->
  ([(AttrKey, EL'AttrDef)] -> STM ()) ->
  STM ()
-- TODO special treatments for interpreter and 3-arg operator:
-- - 1st `callerScope` be of scope object type
-- - rest args be of expr type
defArgArts !eas !opSym !srcExpr !ars = go [] ars
  where
    !eac = el'context eas
    !mwip = el'ContextModule eac
    diags = el'ctx'diags eac

    go ::
      [(AttrKey, EL'AttrDef)] ->
      [ArgReceiver] ->
      ([(AttrKey, EL'AttrDef)] -> STM ()) ->
      STM ()
    go !args [] !exit = exit $ reverse args
    go !args (ar : rest) !exit = case ar of
      RecvArg argAddr@(AttrAddrSrc _ arg'name'span) !maybeRename !maybeDef ->
        case maybeRename of
          Nothing -> defArgArt argAddr maybeDef
          Just (DirectRef !tgtAttr) -> defArgArt tgtAttr maybeDef
          Just
            ref@( IndirectRef
                    tgtExpr@(ExprSrc _ tgt'span)
                    addr@(AttrAddrSrc _ !addr'span)
                  ) -> do
              el'RunTx eas $
                el'AnalyzeExpr tgtExpr $ \ !tgtVal !easDone' -> do
                  -- record as reference symbol, for completion
                  recordAttrRef eac $
                    EL'UnsolvedRef (Just tgtVal) addr'span
                  el'ResolveAttrAddr easDone' addr $ \case
                    Nothing ->
                      -- record as reference symbol, for completion
                      recordAttrRef eac $ EL'UnsolvedRef Nothing addr'span
                    Just !attrKey ->
                      case tgtVal of
                        EL'ObjVal _ms !obj -> do
                          let !cls = el'obj'class obj
                              !objAttrs = el'obj'attrs obj
                          !maybePrevDef <- el'ResolveObjAttr obj attrKey
                          case maybePrevDef of
                            Just !prevDef ->
                              -- record as reference symbol
                              recordAttrRef eac $
                                EL'AttrRef Nothing addr mwip prevDef
                            Nothing -> pure ()
                          !attrAnno <-
                            (newTVar =<<) $
                              tryReadTMVar (el'class'defi cls) >>= \case
                                Nothing -> return Nothing
                                Just !defi ->
                                  return $
                                    odLookup attrKey $ el'class'annos defi
                          let !attrDef =
                                EL'AttrDef
                                  attrKey
                                  NoDocCmt
                                  opSym
                                  addr'span
                                  ( ExprSrc
                                      (AttrExpr ref)
                                      ( SrcRange
                                          (src'start tgt'span)
                                          (src'end addr'span)
                                      )
                                  )
                                  ( EL'Expr $
                                      fromMaybe
                                        ( ExprSrc
                                            (AttrExpr (DirectRef argAddr))
                                            arg'name'span
                                        )
                                        maybeDef
                                  )
                                  attrAnno
                                  Nothing
                          iopdInsert attrKey attrDef objAttrs
                        -- TODO more to do?
                        _ -> pure ()
                  go args rest exit
          Just !badRename -> do
            el'LogDiag
              diags
              el'Error
              (attrRefSpan badRename)
              "bad-re-target"
              "bad argument re-targeting"
            go args rest exit
      RecvRestPkArgs !argAddr -> defArgArt argAddr Nothing
      RecvRestKwArgs !argAddr -> defArgArt argAddr Nothing
      RecvRestPosArgs !argAddr -> defArgArt argAddr Nothing
      where
        defArgArt (AttrAddrSrc (NamedAttr "_") _) _ = go args rest exit
        defArgArt argAddr@(AttrAddrSrc _ arg'name'span) !knownExpr =
          el'ResolveAttrAddr eas argAddr $ \case
            Nothing -> go args rest exit
            Just !argKey -> do
              -- check if it shadows attr from outer scopes
              el'ResolveLexicalAttr
                (el'ctx'scope eac : el'ctx'outers eac)
                argKey
                >>= \case
                  Nothing -> pure ()
                  Just !shadowedDef -> do
                    el'LogDiag
                      diags
                      el'Warning
                      arg'name'span
                      "arg-shadow"
                      "shadows the attribute defined in outer scope"
                    -- record a reference to the shadowed attr
                    let !attrRef =
                          EL'AttrRef
                            Nothing
                            argAddr
                            mwip
                            shadowedDef
                    recordAttrRef eac attrRef

              newTVar Nothing >>= \ !anno ->
                go
                  ( ( argKey,
                      EL'AttrDef
                        argKey
                        NoDocCmt
                        opSym
                        arg'name'span
                        srcExpr
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
                  exit

--

-- | generate completion items at specified location
-- the result will be put into response to `textDocument/completion` request
suggestCompletions ::
  EL'World ->
  Int ->
  Int ->
  EL'ResolvedModule ->
  STM [CompletionItem]
suggestCompletions !elw !line !char !modu =
  case locateAttrRefInModule line char modu of
    Just (EL'UnsolvedRef !maybeTgtVal !addr'span) -> case maybeTgtVal of
      Nothing -> suggestArtsInScope addr'span
      Just !tgtVal -> case tgtVal of
        EL'ObjVal _ms !obj -> suggestObjArts obj addr'span
        EL'ClsVal _ms !cls -> suggestClsArts cls addr'span
        -- TODO support more
        _ -> return []
    Just (EL'AttrRef !maybeTgtVal (AttrAddrSrc _addr !addr'span) _ms _def) ->
      case maybeTgtVal of
        Nothing -> suggestArtsInScope addr'span
        Just !tgtVal -> case tgtVal of
          EL'ObjVal _ms !obj -> suggestObjArts obj addr'span
          EL'ClsVal _ms !cls -> suggestClsArts cls addr'span
          -- TODO support more
          _ -> return []
    --

    Nothing -> suggestArtsInScope cursorInsertRng
  where
    !cursorPos = SrcPos line char
    !cursorInsertRng = SrcRange cursorPos cursorPos

    -- LSP requires the TextEdit to not span multiple lines
    replaceSpan :: SrcRange -> SrcRange
    replaceSpan (SrcRange !addr'start !addr'end) =
      SrcRange addr'start $
        if src'line addr'end == src'line addr'start
          then addr'end
          else addr'start

    suggestArtsInScope :: SrcRange -> STM [CompletionItem]
    suggestArtsInScope !addr'span =
      return $
        concat
          [ suggestScopeArt replace'span
              <$> collectArtsInScopeAt cursorPos (el'modu'scope modu),
            intrinsicSuggestions,
            suggestScopeArt replace'span
              <$> [ (k, def)
                    | (k, def) <- odToList (el'ambient elw),
                      suggestAmbientArt (k, def)
                  ]
          ]
      where
        !replace'span = replaceSpan addr'span
        suggestAmbientArt :: (AttrKey, EL'AttrDef) -> Bool
        suggestAmbientArt (AttrBySym _, _) = True
        suggestAmbientArt (AttrByName !artName, _) =
          not $ "__" `T.isPrefixOf` artName

        !intrinsicSuggestions =
          [ completionToken
              "nil"
              "nil literal"
              "the dreaded nothingness"
              "100", -- category
            completionToken
              "true"
              "true literal"
              "the literal boolean value"
              "100", -- category
            completionToken
              "false"
              "false literal"
              "the literal boolean value"
              "100", -- category
            completionToken
              "sink"
              "sink constructor"
              ( "the `sink` literal will construct a new event sink"
                  <> " each time it is evaluated"
              )
              "100", -- category
            completionToken
              "nan"
              "nan literal"
              "not-a-number, the toxic Decimal value"
              "100", -- category
            completionToken
              "inf"
              "inf literal"
              "the infinite Decimal value, can be negated as `-inf`"
              "100", -- category
            completionToken
              "None"
              "None literal"
              ( "None carries the same semantics as in Python, while it is "
                  <> "technically `None := nil` in Edh"
              )
              "100", -- category
            completionToken
              "Nothing"
              "Nothing literal"
              ( "Nothing carries the same semantics as in BASIC, while it is "
                  <> "technically `Nothing := nil` in Edh"
              )
              "100", -- category
            completionToken
              "NA"
              "NA literal"
              ( "not-applicable, the toxic default value, "
                  <> "it is technically `default nil"
              )
              "100", -- category
            completionToken
              "EQ"
              "literal for _equal_"
              ( "EQ carries the same semantics as in Haskell, "
                  <> "while being exactly the same value in the host env"
              )
              "100", -- category
            completionToken
              "LT"
              "literal for _less-than_"
              ( "LT carries the same semantics as in Haskell, "
                  <> "while being exactly the same value in the host env"
              )
              "100", -- category
            completionToken
              "GT"
              "literal for _greater-than_"
              ( "GT carries the same semantics as in Haskell, "
                  <> "while being exactly the same value in the host env"
              )
              "100" -- category
          ]

    suggestScopeArt :: SrcRange -> (AttrKey, EL'AttrDef) -> CompletionItem
    suggestScopeArt !replace'span (!key, !def) =
      completionText
        label
        detail
        mdContents
        cate
        replace'span
      where
        !label = attrKeyStr key
        !detail = attrKeyStr $ el'attr'def'key def -- use better text
        !mdContents =
          T.intercalate "\n***\n" $ T.intercalate "\n" <$> el'AttrDoc def
        !cate = case True of
          -- magic names, should seldom be written out
          True | "__" `T.isPrefixOf` label -> "999"
          -- TODO more to categorize wrt sorting
          _ -> "000" -- vanilla artifacts
          --

    --
    suggestMemberArt ::
      Text ->
      SrcRange ->
      (AttrKey, EL'AttrDef) ->
      CompletionItem
    suggestMemberArt !typeName !replace'span (!key, !def) =
      completionText
        label
        detail
        mdContents
        cate
        replace'span
      where
        !label = attrKeyStr key
        !detail = typeName <> "." <> attrKeyStr (el'attr'def'key def)
        !mdContents =
          T.intercalate "\n***\n" $ T.intercalate "\n" <$> el'AttrDoc def
        !cate = case True of
          -- magic names, should seldom be written out
          True | "__" `T.isPrefixOf` label -> "999"
          -- TODO more to categorize wrt sorting
          _ -> "000" -- vanilla artifacts
          --

    --
    suggestObjArts :: EL'Object -> SrcRange -> STM [CompletionItem]
    suggestObjArts !obj !addr'span = do
      !instAttrs <- iopdToList (el'obj'attrs obj)
      !clsAttrs <- iopdToList (el'class'attrs cls)
      -- TODO include mro, dedup
      return $
        suggestMemberArt typeName (replaceSpan addr'span)
          <$> instAttrs ++ clsAttrs
      where
        !cls = el'obj'class obj
        !typeName = attrKeyStr $ el'class'name cls

    suggestClsArts :: EL'Class -> SrcRange -> STM [CompletionItem]
    suggestClsArts !cls !addr'span = do
      !clsAttrs <- iopdToList (el'class'attrs cls)
      -- TODO include mro, dedup
      return $
        suggestMemberArt typeName (replaceSpan addr'span)
          <$> clsAttrs
      where
        !typeName = attrKeyStr $ el'class'name cls

--
