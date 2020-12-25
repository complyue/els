module Language.Edh.Meta.Analyze where

-- import Debug.Trace

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
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.EHI
import Language.Edh.Meta.AtTypes
import Language.Edh.Meta.Model
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
      unsafeIOToSTM (resolveAbsoluteImport nomSpec ".") >>= \case
        Left !err -> throwEdh ets PackageError err
        Right (_moduName, _moduPath, !moduFile) -> runEdhTx ets $
          el'LocateModuleByFile elw (T.pack moduFile) $ \ !ms _ets ->
            exitEdh ets exit ms
  where
    !nomSpec = normalizeImportSpec absModuSpec

el'LocateModuleByFile :: EL'World -> Text -> EdhProc EL'ModuSlot
el'LocateModuleByFile !elw !moduFile !exit !ets =
  if not $ ".edh" `T.isSuffixOf` moduFile
    then throwEdh ets UsageError $ "not a .edh file: " <> moduFile
    else
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
            !parsing <- newEmptyTMVar
            !resolution <- newEmptyTMVar
            let !ms =
                  EL'ModuSlot
                    home
                    name
                    (SrcDoc absFile)
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
                                    T.stripSuffix ".edh" $ T.pack relPath,
                                  T.pack absFile
                                )
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
      Right (_moduName, _moduPath, !moduFile) -> runEdhTx ets $
        el'LocateModuleByFile elw (T.pack moduFile) $ \ !ms _ets ->
          el'Exit eas exit $ Right ms
  where
    elw = el'world eas
    ets = el'ets eas
    SrcDoc !docFile = el'modu'doc msFrom
    !nomSpec = normalizeImportSpec impSpec

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
el'InvalidateModule :: Bool -> EL'ModuSlot -> EdhProc ()
el'InvalidateModule !srcChanged !ms !exit !ets = do
  when srcChanged $ void $ tryTakeTMVar (el'modu'parsing ms)
  tryTakeTMVar reso >>= \case
    Nothing -> pure ()
    Just (EL'ModuResolving !resolving _acts) ->
      readTVar (el'resolving'dependants resolving)
        >>= invalidateDeps (el'resolving'dependants resolving) . Map.toList
    Just (EL'ModuResolved !resolved) ->
      readTVar (el'modu'dependants resolved)
        >>= invalidateDeps (el'modu'dependants resolved) . Map.toList
  where
    !reso = el'modu'resolution ms
    invalidateDeps :: TVar (HashMap EL'ModuSlot Bool) -> [(EL'ModuSlot, Bool)] -> STM ()
    invalidateDeps !dependants !deps = go [] deps
      where
        go :: [(EL'ModuSlot, Bool)] -> [(EL'ModuSlot, Bool)] -> STM ()
        go !upds [] = do
          unless (null upds) $
            modifyTVar' dependants $
              -- todo maybe should delete instead of update here?
              -- in case some module file is deleted, this'll leak?
              Map.union (Map.fromList upds)
          exitEdh ets exit ()
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

-- | obtain the result as the specified module is parsed
asModuleParsed :: EL'ModuSlot -> EdhProc EL'ParsedModule
asModuleParsed !ms !exit !ets =
  tryReadTMVar parsingVar >>= \case
    Nothing -> do
      !parsedVar <- newEmptyTMVar
      -- the put will retry if parsingVar has been changed by others
      -- concurrently, so no duplicate effort would incur here
      putTMVar parsingVar (EL'ModuParsing parsedVar)
      -- todo maybe try harder to guarantee 'parsedVar' will always be filled.
      -- bracket with STM monad is not correct as multiple txs it will span;
      -- using Edh finally block may be the way, but we're already doing that
      -- in 'doParseModule', not sure anything to be done here so.
      doParseModule $ \ !parsed -> do
        -- install the parsed record
        putTMVar parsedVar parsed
        tryTakeTMVar parsingVar >>= \case
          Just (EL'ModuParsing parsedVar')
            | parsedVar' == parsedVar ->
              -- the most expected scenario
              putTMVar parsingVar $ EL'ModuParsed parsed
          Just !other ->
            -- invalidated & new analysation wip
            void $ tryPutTMVar parsingVar other
          _ ->
            -- invalidated meanwhile
            return ()

        -- return from this procedure
        exitEdh ets exit parsed
    Just (EL'ModuParsing !parsedVar) -> do
      -- parsing by some other thread,
      -- blocking wait a result in next tx
      runEdhTx ets $ edhContSTM $ readTMVar parsedVar >>= exitEdh ets exit
    Just (EL'ModuParsed !parsed) -> exitEdh ets exit parsed
  where
    !parsingVar = el'modu'parsing ms

    doParseModule :: (EL'ParsedModule -> STM ()) -> STM ()
    doParseModule !exit' = edhCatch
      ets
      (parseModuleOnDisk $ el'modu'doc ms)
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

parseModuleOnDisk :: SrcDoc -> EdhProc EL'ParsedModule
parseModuleOnDisk moduDoc@(SrcDoc !moduFile) !exit !ets =
  unsafeIOToSTM
    ( streamDecodeUtf8With lenientDecode
        <$> B.readFile
          ( T.unpack
              moduFile
          )
    )
    >>= \case
      Some !moduSource _ _ -> parseModuleSource moduSource moduDoc exit ets

-- | fill in module source on the fly, usually pending save from an IDE editor
--
-- todo track document version to cancel parsing attempts for old versions
el'FillModuleSource :: Text -> EL'ModuSlot -> EdhProc EL'ParsedModule
el'FillModuleSource !moduSource !ms !exit !ets =
  -- invalidate parsing/resolution results of this module and all dependants
  runEdhTx ets $
    el'InvalidateModule True ms $ \() _ets -> do
      void $ tryTakeTMVar parsingVar
      -- now parse the supplied source and get the result,
      -- then try install only if it's still up-to-date
      !parsedVar <- newEmptyTMVar
      -- the put will retry if parsingVar has been changed by others
      -- concurrently, so no duplicate effort would incur here
      putTMVar parsingVar (EL'ModuParsing parsedVar)

      -- parse & install the result
      doParseModule $ \ !parsed -> do
        putTMVar parsedVar parsed
        tryTakeTMVar parsingVar >>= \case
          Just (EL'ModuParsing parsedVar')
            | parsedVar' == parsedVar ->
              -- the most expected scenario
              putTMVar parsingVar $ EL'ModuParsed parsed
          -- invalidated & new analysation wip
          Just !other -> putTMVar parsingVar other
          -- invalidated meanwhile
          _ -> return ()

        -- return from this procedure
        exitEdh ets exit parsed
  where
    !parsingVar = el'modu'parsing ms

    doParseModule :: (EL'ParsedModule -> STM ()) -> STM ()
    doParseModule !exit' = edhCatch
      ets
      (parseModuleSource moduSource $ el'modu'doc ms)
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

parseModuleSource :: Text -> SrcDoc -> EdhProc EL'ParsedModule
parseModuleSource !moduSource (SrcDoc !moduFile) !exit !ets =
  -- TODO use partial parser, and gather diags
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

-- | obtain the result as the specified module is resolved
asModuleResolved :: EL'World -> EL'ModuSlot -> EdhProc EL'ResolvedModule
asModuleResolved !world !ms !exit =
  asModuleResolving world ms $ \case
    EL'ModuResolving _resolving !resolvedVar -> \ !ets ->
      -- blocking wait a result in next tx
      runEdhTx ets $ edhContSTM $ readTMVar resolvedVar >>= exitEdh ets exit
    EL'ModuResolved !resolved -> exitEdhTx exit resolved

asModuleResolving :: EL'World -> EL'ModuSlot -> EdhProc EL'ModuResolution
asModuleResolving !world !ms !exit !ets =
  tryReadTMVar resoVar >>= \case
    Nothing -> do
      !resolvedVar <- newEmptyTMVar
      !exts <- newTVar []
      !exps <- iopdEmpty
      !dependencies <- newTVar Map.empty
      !diags <- newTVar []
      !dependants <- newTVar Map.empty
      let !resolving =
            EL'ResolvingModu
              exts
              exps
              dependencies
              diags
              dependants
      -- the put will retry if parsingVar has been changed by others
      -- concurrently, so no duplicate effort would incur here
      putTMVar resoVar (EL'ModuResolving resolving resolvedVar)
      -- todo maybe try harder to guarantee 'resolvedVar' will always be filled.
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
    Just !reso -> exitEdh ets exit reso
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
  let !modu'name = el'modu'name ms
      !name'def =
        EL'AttrDef
          (AttrByName "__name__")
          Nothing
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
          Nothing -> case T.stripSuffix ".edh" modu'file of
            Just !path -> path
            Nothing -> modu'file
      !file'def =
        EL'AttrDef
          (AttrByName "__file__")
          Nothing
          "<module>"
          noSrcRange
          (ExprSrc (LitExpr (StringLiteral modu'file)) noSrcRange)
          (EL'Const (EdhString modu'file))
          maoAnnotation
          Nothing
      !path'def =
        EL'AttrDef
          (AttrByName "__path__")
          Nothing
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
  !ctxSyms <- newTVar []
  !branchAttrs <- iopdFromList $ odToList builtinAttrs
  !moduAttrs <- iopdClone branchAttrs
  !moduEffs <- iopdEmpty
  !moduAnnos <- iopdEmpty
  !branchRegions <- newTVar [EL'RegionWIP beginningSrcPos builtinAttrs]
  !moduScopes <- newTVar []
  !moduRegions <- newTVar []
  let !bwip =
        EL'BranchWIP
          branchAttrs
          moduEffs
          moduAnnos
          branchRegions
      !pwip =
        EL'ProcWIP
          bwip
          moduAttrs
          (el'modu'exts'wip resolving)
          (el'modu'exps'wip resolving)
          moduScopes
          moduRegions
      !eac =
        EL'Context
          { el'ctx'scope = EL'InitModule ms resolving pwip,
            el'ctx'outers = [],
            el'ctx'pure = False,
            el'ctx'exporting = False,
            el'ctx'eff'defining = False,
            el'ctx'symbols = ctxSyms,
            el'ctx'diags = el'resolving'diags resolving
          }
      !eas =
        EL'AnalysisState
          { el'world = world,
            el'context = eac,
            el'ets = ets
          }

  el'RunTx eas $
    el'AnalyzeStmts body $ \_ !easDone -> do
      let !eacDone = el'context easDone
          !swipDone = el'ctx'scope eacDone
          !pwipDone = el'ProcWIP swipDone
          !bwipDone = el'scope'branch'wip pwipDone
      !regions'wip <-
        fmap
          ( \(EL'RegionWIP !reg'start !reg'arts) ->
              EL'Region
                (SrcRange reg'start moduEnd)
                reg'arts
          )
          <$> readTVar (el'branch'regions'wip bwipDone)
      !innerScopes <- readTVar moduScopes
      !regions <-
        (regions'wip ++)
          <$> readTVar (el'scope'regions'wip pwipDone)
      !modu'symbols <- sortOn attrSymKey <$> readTVar ctxSyms

      !diags <- readTVar $ el'resolving'diags resolving
      !moduExps <- iopdSnapshot $ el'modu'exps'wip resolving
      !dependencies <- readTVar $ el'modu'dependencies'wip resolving
      let !el'scope =
            EL'Scope
              { el'scope'span = SrcRange beginningSrcPos moduEnd,
                el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                el'scope'regions = V.fromList $! reverse regions
              }
      exitEdh ets exit $
        EL'ResolvedModule
          el'scope
          moduExps
          (V.fromList modu'symbols)
          (reverse diags)
          dependencies
          (el'resolving'dependants resolving)
  where
    moduEnd :: SrcPos
    moduEnd = go body
      where
        go [] = beginningSrcPos
        go [StmtSrc _ !last'stmt'span] = src'end last'stmt'span
        go (_ : rest'stmts) = go rest'stmts

-- | pack arguments
el'PackArgs :: ArgsPacker -> EL'Analysis EL'ArgsPack
el'PackArgs (ArgsPacker !argSndrs _) !exit !eas =
  el'RunTx easPure $ collectArgs [] [] argSndrs
  where
    !eac = el'context eas
    !easPure = eas {el'context = eac {el'ctx'pure = True}}
    !originPure = el'ctx'pure eac

    collectArgs :: [EL'Value] -> [(AttrKey, EL'Value)] -> [ArgSender] -> EL'Tx
    collectArgs !args !kwargs [] = \ !easDone ->
      el'Exit
        easDone
          { el'context = (el'context easDone) {el'ctx'pure = originPure}
          }
        exit
        $ EL'ArgsPack (reverse args) $ odFromList $ reverse kwargs
    collectArgs !args !kwargs (asndr : rest) = case asndr of
      UnpackPosArgs !ax -> el'AnalyzeExpr Nothing ax $ \_argVal ->
        -- TODO try analyze the unpacking
        collectArgs args kwargs rest
      UnpackKwArgs !ax -> el'AnalyzeExpr Nothing ax $ \_argVal ->
        -- TODO try analyze the unpacking
        collectArgs args kwargs rest
      UnpackPkArgs !ax -> el'AnalyzeExpr Nothing ax $ \_argVal ->
        -- TODO try analyze the unpacking
        collectArgs args kwargs rest
      SendPosArg !ax -> el'AnalyzeExpr Nothing ax $ \ !argVal ->
        collectArgs (argVal : args) kwargs rest
      SendKwArg !argAddr !ax -> \ !easDone ->
        el'ResolveAttrAddr easDone argAddr >>= \case
          Nothing -> el'RunTx easDone $ collectArgs args kwargs rest
          Just !argKey -> el'RunTx easDone $
            el'AnalyzeExpr Nothing ax $ \ !argVal ->
              collectArgs args ((argKey, argVal) : kwargs) rest

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
el'AnalyzeStmt (StmtSrc (ExprStmt !expr !docCmt) !stmt'span) !exit !eas =
  el'RunTx eas $ el'AnalyzeExpr docCmt (ExprSrc expr stmt'span) exit
--

-- a let statement
el'AnalyzeStmt
  let'stmt@(StmtSrc (LetStmt !argsRcvr !argsSndr) !stmt'span)
  !exit
  !eas =
    el'RunTx eas $
      el'PackArgs argsSndr $ \apk@(EL'ArgsPack !args !kwargs) _eas ->
        case argsRcvr of
          PackReceiver !rcvrs -> doRecv apk rcvrs
          SingleReceiver !rcvr -> doRecv apk [rcvr]
          WildReceiver -> do
            unless (null args) $
              el'LogDiag
                diags
                el'Error
                stmt'span
                "let-wild-pos-arg"
                "letting positional argument(s) into wild receiver"

            -- receive each kwargs
            forM_ (odToList kwargs) $ \(!k, !v) -> recvOne' stmt'span k v

            -- record a region after this let statement, for current branch
            iopdSnapshot (el'branch'attrs'wip bwip)
              >>= modifyTVar' (el'branch'regions'wip bwip) . (:)
                . EL'RegionWIP (src'end stmt'span)

            el'Exit eas exit $ EL'Const nil
    where
      {- HLINT ignore "Reduce duplication" -}
      !eac = el'context eas
      diags = el'ctx'diags eac
      !swip = el'ctx'scope eac
      !pwip = el'ProcWIP swip
      !bwip = el'scope'branch'wip pwip

      doRecv :: EL'ArgsPack -> [ArgReceiver] -> STM ()
      doRecv (EL'ArgsPack !args !kwargs) !rcvrs =
        go args kwargs rcvrs $ \ !args' !kwargs' -> do
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
              . EL'RegionWIP (src'end stmt'span)

          el'Exit eas exit $ EL'Const nil

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
          recvOne addr $ EL'Apk $ EL'ArgsPack args odEmpty
          done [] kwargs
        RecvRestKwArgs !addr -> do
          recvOne addr $ EL'Apk $ EL'ArgsPack [] kwargs
          done args odEmpty
        RecvRestPkArgs !addr -> do
          recvOne addr $ EL'Apk $ EL'ArgsPack args kwargs
          done [] odEmpty
        RecvArg addr@(AttrAddrSrc _ arg'span) !maybeRename maybeDef ->
          let goRecv :: AttrAddrSrc -> (AttrKey -> EL'Value -> STM ()) -> STM ()
              goRecv !recvAddr !received =
                el'ResolveAttrAddr eas recvAddr >>= \case
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
                          el'LogDiag
                            diags
                            el'Error
                            arg'span
                            "missing-arg"
                            "missing argument"
                          done args kwargs
                        Just !defExpr -> el'RunTx
                          eas {el'context = eac {el'ctx'pure = True}}
                          $ el'AnalyzeExpr Nothing defExpr $
                            \ !defVal _eas -> do
                              received recvKey defVal
                              done args kwargs
           in case maybeRename of
                Nothing -> goRecv addr $ recvOne' arg'span
                Just (DirectRef !addr') ->
                  goRecv addr $ \_recvKey -> recvOne addr'
                Just IndirectRef {} -> done args kwargs
                _ -> do
                  el'LogDiag
                    diags
                    el'Error
                    arg'span
                    "invalid-target"
                    "invalid let target"
                  done args kwargs

      recvOne :: AttrAddrSrc -> EL'Value -> STM ()
      recvOne addr@(AttrAddrSrc _ !addr'span) !v =
        el'ResolveAttrAddr eas addr >>= \case
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
                Nothing
                "<let>"
                focus'span
                (ExprSrc (BlockExpr [let'stmt]) stmt'span)
                attrVal
                attrAnno
                prevDef
        -- record as definition symbol of current scope
        recordCtxSym eac $ EL'DefSym attrDef
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
          iopdInsert attrKey attrDef $ el'scope'exps'wip pwip
--

-- effect defining
el'AnalyzeStmt (StmtSrc (EffectStmt !effs !docCmt) _stmt'span) !exit !eas =
  el'RunTx eas {el'context = eac {el'ctx'eff'defining = True}} $
    el'AnalyzeExpr docCmt effs $ \_ _eas -> el'Exit eas exit $ EL'Const nil
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

    !swip = el'ctx'scope eac
    !pwip = el'ProcWIP swip
-- !bwip = el'scope'branch'wip pwip
--

-- go
el'AnalyzeStmt (StmtSrc (GoStmt !expr) _stmt'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing expr $ const $ el'ExitTx exit $ EL'Const nil
--

-- defer
el'AnalyzeStmt (StmtSrc (DeferStmt !expr) _stmt'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing expr $ const $ el'ExitTx exit $ EL'Const nil
--

-- perceive
el'AnalyzeStmt (StmtSrc (PerceiveStmt !expr !body) _stmt'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing expr $
      const $
        el'AnalyzeStmt body $
          const $ el'ExitTx exit $ EL'Const nil
--

-- while
el'AnalyzeStmt (StmtSrc (WhileStmt !expr !body) _stmt'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing expr $
      const $ el'AnalyzeStmt body $ const $ el'ExitTx exit $ EL'Const nil
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
el'AnalyzeStmt (StmtSrc (ReturnStmt !expr) _stmt'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing expr $
      const $ el'ExitTx exit $ EL'Return expr
--

-- throw
el'AnalyzeStmt (StmtSrc (ThrowStmt !expr) _stmt'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing expr $
      const $ el'ExitTx exit $ EL'Throw expr
--

-- rethrow
el'AnalyzeStmt (StmtSrc RethrowStmt _stmt'span) !exit !eas =
  el'Exit eas exit EL'Rethrow
--

-- the rest of statements not analyzed
el'AnalyzeStmt _stmt !exit !eas = el'Exit eas exit $ EL'Const nil

-- * expression analysis

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
    go [!expr] !vals = el'AnalyzeExpr Nothing expr $ \ !result !easDone ->
      el'Exit
        easDone
          { el'context = (el'context easDone) {el'ctx'pure = originPure}
          }
        exit
        $! reverse
        $ result : vals
    go (expr : rest) !vals = el'AnalyzeExpr Nothing expr $ \ !r ->
      go rest (r : vals)

-- | literal to analysis time value
el'LiteralValue :: Literal -> STM EL'Value
el'LiteralValue = \case
  DecLiteral !v -> return $ EL'Const (EdhDecimal v)
  StringLiteral !v -> return $ EL'Const (EdhString v)
  BoolLiteral !v -> return $ EL'Const (EdhBool v)
  NilLiteral -> return $ EL'Const nil
  TypeLiteral !v -> return $ EL'Const (EdhType v)
  SinkCtor -> EL'Const . EdhSink <$> newEventSink
  ValueLiteral !v -> return $ EL'Const v

-- | analyze an expression in context
el'AnalyzeExpr :: Maybe DocComment -> ExprSrc -> EL'Analysis EL'Value
--

-- block
el'AnalyzeExpr _docCmt (ExprSrc (BlockExpr !stmts) !blk'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeStmts stmts $ \ !blkResult !easDone -> do
      let closeBlk = do
            let !eacDone = el'context easDone
                !swipDone = el'ctx'scope eacDone
                !pwipDone = el'ProcWIP swipDone
                !bwipDone = el'scope'branch'wip pwipDone
            -- close all pending regions
            !regions'wip <-
              fmap
                ( \(EL'RegionWIP !reg'start !reg'arts) ->
                    EL'Region
                      (SrcRange reg'start (src'end blk'span))
                      reg'arts
                )
                <$> swapTVar (el'branch'regions'wip bwipDone) []
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
              (EL'RegionWIP (src'end blk'span) attrs :)

          el'Exit easDone exit blkResult
--

-- direct attribute addressing
el'AnalyzeExpr
  _docCmt
  xsrc@( ExprSrc
           (AttrExpr (DirectRef addr@(AttrAddrSrc _ !addr'span)))
           _expr'span
         )
  !exit
  !eas =
    el'ResolveAttrAddr eas addr >>= \case
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
            returnAsExpr
          Just !attrDef -> do
            -- record as referencing symbol of outer scope
            let !attrRef = EL'AttrRef addr attrDef
            recordCtxSym eac $ EL'RefSym attrRef

            el'Exit eas exit $ el'attr'def'value attrDef
    where
      !eac = el'context eas
      diags = el'ctx'diags eac
      returnAsExpr = el'Exit eas exit $ EL'Expr xsrc
--

-- indirect attribute addressing (dot-notation)
el'AnalyzeExpr
  _docCmt
  xsrc@( ExprSrc
           (AttrExpr (IndirectRef !tgtExpr addr@(AttrAddrSrc _ !addr'span)))
           _expr'span
         )
  !exit
  !eas = el'RunTx eas $
    el'AnalyzeExpr Nothing tgtExpr $ \ !tgtVal _eas ->
      el'ResolveAttrAddr eas addr >>= \case
        Nothing -> returnAsExpr
        Just !refKey -> case tgtVal of
          -- object instance attribute addressing
          EL'ObjVal !cls -> case odLookup refKey $ el'inst'attrs cls of
            Nothing -> case odLookup refKey $ el'class'attrs cls of
              Nothing -> do
                el'LogDiag
                  diags
                  el'Error
                  addr'span
                  "no-obj-attr"
                  "no such object attribute"
                returnAsExpr
              Just !attrDef -> do
                -- record as referencing symbol of outer scope
                let !attrRef = EL'AttrRef addr attrDef
                recordCtxSym eac $ EL'RefSym attrRef

                el'Exit eas exit $ el'attr'def'value attrDef
            Just !attrDef -> do
              -- record as referencing symbol of outer scope
              let !attrRef = EL'AttrRef addr attrDef
              recordCtxSym eac $ EL'RefSym attrRef

              el'Exit eas exit $ el'attr'def'value attrDef
          --

          -- class attribute addressing
          EL'ClsVal !cls -> case odLookup refKey (el'class'attrs cls) of
            Nothing -> do
              el'LogDiag
                diags
                el'Error
                addr'span
                "no-cls-attr"
                "no such class attribute"
              returnAsExpr
            Just !attrDef -> do
              -- record as referencing symbol of outer scope
              let !attrRef = EL'AttrRef addr attrDef
              recordCtxSym eac $ EL'RefSym attrRef

              el'Exit eas exit $ el'attr'def'value attrDef
          --

          -- EL'Const (EdhObject _obj) -> undefined -- TODO this possible ?
          -- EL'External _ms _attrDef -> undefined -- TODO this possible ?
          -- EL'ModuVal !ms -> undefined -- TODO handle this
          -- EL'ProcVal !p -> undefined -- TODO handle this
          -- EL'Const (EdhDict (Dict _ _ds)) -> undefined -- TODO handle this
          -- EL'Const (EdhList (List _ _ls)) -> undefined -- TODO handle this
          _ -> returnAsExpr -- unrecognized value
    where
      !eac = el'context eas
      diags = el'ctx'diags eac
      returnAsExpr = el'Exit eas exit $ EL'Expr xsrc
--

-- infix operator application
el'AnalyzeExpr
  !docCmt
  xsrc@( ExprSrc
           ( InfixExpr
               !opSym
               lhExpr@(ExprSrc !lhx !lh'span)
               rhExpr@(ExprSrc _rhx !rh'span)
             )
           !expr'span
         )
  !exit
  !eas = case opSym of
    -- comparisons
    "==" -> doCmp
    "!=" -> doCmp
    ">=" -> doCmp
    "<=" -> doCmp
    ">" -> doCmp
    "<" -> doCmp
    "is" -> doCmp
    "is not" -> doCmp
    "?<=" -> doCmp
    --

    -- assignment
    _ | "=" `T.isSuffixOf` opSym -> doAssign
    --

    -- branch
    "->" -> doBranch
    --

    -- method/generator arrow procedure
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

    -- annotation
    "::" -> case lhExpr of
      ExprSrc (AttrExpr (DirectRef !addr)) _ ->
        el'ResolveAttrAddr eas addr >>= \case
          Nothing -> returnAsExpr eas
          Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
          Just !attrKey -> do
            let !attrAnno = EL'AttrAnno rhExpr docCmt
            iopdInsert attrKey attrAnno (el'branch'annos'wip bwip)
            el'Exit eas exit $ EL'Const nil
      ExprSrc _ !bad'anno'span -> do
        el'LogDiag
          diags
          el'Warning
          bad'anno'span
          "bad-anno"
          "bad annotation"
        returnAsExpr eas
    --

    -- left-dropping annotation
    "!" -> el'RunTx eas $ el'AnalyzeExpr docCmt rhExpr exit
    --

    -- TODO special treatment of ($) (|) (&) etc. ?

    -- other operations without special treatment
    _ ->
      el'RunTx eas $
        el'AnalyzeExpr Nothing lhExpr $
          const $
            el'AnalyzeExpr Nothing rhExpr $ const returnAsExpr
            --

            --
    where
      !eac = el'context eas
      diags = el'ctx'diags eac
      !swip = el'ctx'scope eac
      !pwip = el'ProcWIP swip
      !bwip = el'scope'branch'wip pwip
      returnAsExpr = el'ExitTx exit $ EL'Expr xsrc

      doCmp :: STM ()
      doCmp =
        el'RunTx eas $
          el'AnalyzeExpr Nothing lhExpr $
            const $
              el'AnalyzeExpr Nothing rhExpr $ const returnAsExpr

      doAssign :: STM ()
      doAssign = el'RunTx eas $
        el'AnalyzeExpr Nothing rhExpr $ \ !rhVal !easDone -> do
          case lhExpr of
            ExprSrc (AttrExpr (DirectRef addr@(AttrAddrSrc _ !addr'span))) _ ->
              el'ResolveAttrAddr easDone addr >>= \case
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
                  unless (el'ctx'pure eac) $ do
                    if el'ctx'eff'defining eac
                      then do
                        let !effs = el'branch'effs'wip bwip
                        case rhVal of
                          EL'Const EdhNil -> iopdDelete attrKey effs
                          _ -> iopdInsert attrKey attrDef effs
                      else do
                        let !attrs = el'branch'attrs'wip bwip
                        if el'IsNil rhVal && "=" == opSym
                          then do
                            iopdDelete attrKey $ el'scope'attrs'wip pwip
                            iopdDelete attrKey attrs
                            iopdSnapshot attrs
                              >>= modifyTVar' (el'branch'regions'wip bwip) . (:)
                                . EL'RegionWIP (src'end expr'span)
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
                                    . EL'RegionWIP (src'end expr'span)
                              _ -> pure ()
                    when (el'ctx'exporting eac) $
                      iopdInsert attrKey attrDef $ el'scope'exps'wip pwip
                  --

                  if "=" == opSym || ":=" == opSym
                    then do
                      -- record as definition symbol of current scope
                      recordCtxSym eac $ EL'DefSym attrDef
                      el'Exit easDone exit rhVal
                    else case maybePrevDef of
                      Just !prevDef -> do
                        -- record as reference symbol of current scope
                        let !attrRef = EL'AttrRef addr prevDef
                        recordCtxSym eac $ EL'RefSym attrRef
                        returnAsExpr easDone
                      Nothing -> do
                        -- record as definition symbol of current scope
                        recordCtxSym eac $ EL'DefSym attrDef
                        returnAsExpr easDone
            ExprSrc (AttrExpr (IndirectRef !tgtExpr !addr)) _expr'span ->
              el'RunTx easDone $
                el'AnalyzeExpr Nothing tgtExpr $ \_tgtVal !easDone' -> do
                  -- TODO add to lh obj (esp. this) attrs for (=)
                  --      other cases ?
                  void $ el'ResolveAttrAddr easDone' addr
                  returnAsExpr easDone'
            ExprSrc (IndexExpr !idxExpr !tgtExpr) _expr'span ->
              el'RunTx easDone $
                el'AnalyzeExpr Nothing idxExpr $
                  const $
                    el'AnalyzeExpr Nothing tgtExpr $ const returnAsExpr
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
              InfixExpr "|" (ExprSrc !matchExpr _) !guardExpr ->
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
                          Nothing
                          opSym
                          (exprSrcSpan attrExpr)
                          xsrc
                          (EL'Expr attrExpr)
                          attrAnno
                          maybePrevDef
                  go rest ((attrKey, attrDef) : kds)

            defDfAttrs ::
              EL'Artifacts ->
              [ArgSender] ->
              ( [(AttrKey, EL'AttrDef)] ->
                STM ()
              ) ->
              STM ()
            defDfAttrs !arts !sndrs !daExit = go sndrs []
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
                        el'ResolveAttrAddr eas rcvAttr >>= \case
                          Nothing -> go rest kds
                          Just !key -> do
                            let !attrDef =
                                  EL'AttrDef
                                    key
                                    Nothing
                                    opSym
                                    arg'span
                                    xsrc
                                    ( maybe
                                        (EL'Expr attrExpr)
                                        el'attr'def'value
                                        $ odLookup key arts
                                    )
                                    attrAnno
                                    Nothing
                            go rest $ (key, attrDef) : kds
                    SendKwArg
                      !srcAttr
                      attrExpr@( ExprSrc
                                   (AttrExpr (DirectRef !tgtAttr))
                                   !arg'span
                                 ) ->
                        el'ResolveAttrAddr eas srcAttr >>= \case
                          Nothing -> go rest kds
                          Just !srcKey ->
                            el'ResolveAttrAddr eas tgtAttr >>= \case
                              Nothing -> go rest kds
                              Just !tgtKey -> do
                                let !attrDef =
                                      EL'AttrDef
                                        tgtKey
                                        Nothing
                                        opSym
                                        arg'span
                                        xsrc
                                        ( maybe
                                            (EL'Expr attrExpr)
                                            el'attr'def'value
                                            $ odLookup srcKey arts
                                        )
                                        attrAnno
                                        Nothing
                                go rest $ (srcKey, attrDef) : kds
                    _ -> do
                      el'LogDiag
                        diags
                        el'Error
                        (argSenderSpan sndr)
                        "bad-data-field"
                        "bad data class field extractor"
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
                    el'AnalyzeExpr Nothing rhExpr $
                      \ !rhResult !easDone -> do
                        -- TODO fill annos of ps from branchAnnos now
                        case rhResult of
                          EL'Const EdhFallthrough -> do
                            -- this branch leaks to its following code
                            !prevRegions <-
                              readTVar
                                (el'branch'regions'wip bwip)
                            modifyTVar' branchRegions (++ prevRegions)
                            el'Exit easDone exit $ EL'Expr xsrc
                          _ -> do
                            -- this branch closes
                            !regions <-
                              fmap
                                ( \(EL'RegionWIP !reg'start !reg'arts) ->
                                    EL'Region
                                      (SrcRange reg'start (src'end rh'span))
                                      reg'arts
                                )
                                <$> readTVar branchRegions
                            modifyTVar' (el'scope'regions'wip pwip) (regions ++)
                            el'Exit eas exit $ EL'Expr xsrc

              case maybeGuardExpr of
                Nothing -> el'RunTx easBranch analyzeContent
                Just !guardExpr ->
                  el'RunTx easBranch $
                    el'AnalyzeExpr Nothing guardExpr $ const analyzeContent

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
                            Nothing
                            opSym
                            p1Span
                            xsrc
                            (EL'Expr p1Expr)
                            p1Anno
                            Nothing
                    analyzeBranch $! (p1Key, p1Def) : defs
                InfixExpr
                  ":"
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
                            Nothing
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
                el'ResolveAttrAddr eas valAddr >>= \case
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
                el'AnalyzeExpr Nothing clsExpr $
                  \ !clsResult _eas -> case clsResult of
                    EL'ClsVal !clsVal ->
                      defDfAttrs (el'class'attrs clsVal) apkr analyzeBranch
                    _ -> defDfAttrs odEmpty apkr analyzeBranch
            -- { class( field1, field2, ... ) = instAddr } -- fields by
            -- class again, but receive the matched object as well
            -- __match__ magic from the class works here
            [ StmtSrc
                ( ExprStmt
                    ( InfixExpr
                        "="
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
                el'AnalyzeExpr Nothing clsExpr $
                  \ !clsResult _eas -> case clsResult of
                    EL'ClsVal !clsVal ->
                      defDfAttrs (el'class'attrs clsVal) apkr $ \ !dfs ->
                        el'ResolveAttrAddr eas instAddr >>= \case
                          Nothing -> analyzeBranch dfs
                          Just !instKey -> do
                            !anno <- newTVar Nothing
                            let !attrDef =
                                  EL'AttrDef
                                    instKey
                                    Nothing
                                    opSym
                                    inst'span
                                    instExpr
                                    (EL'ObjVal clsVal)
                                    anno
                                    Nothing
                            analyzeBranch $ dfs ++ [(instKey, attrDef)]
                    _ -> defDfAttrs odEmpty apkr $ \ !dfs ->
                      el'ResolveAttrAddr eas instAddr >>= \case
                        Nothing -> analyzeBranch dfs
                        Just !instKey -> do
                          !anno <- newTVar Nothing
                          let !attrDef =
                                EL'AttrDef
                                  instKey
                                  Nothing
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
                        [ ( AddrDictKey !clsRef,
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
                el'ResolveAttrAddr eas instAddr >>= \case
                  Nothing -> analyzeBranch []
                  Just !instKey -> el'RunTx eas $
                    el'AnalyzeExpr
                      Nothing
                      (ExprSrc (AttrExpr clsRef) (attrRefSpan clsRef))
                      $ \ !clsResult _eas -> case clsResult of
                        EL'ClsVal !clsVal -> do
                          !anno <- newTVar Nothing
                          let !attrDef =
                                EL'AttrDef
                                  instKey
                                  Nothing
                                  opSym
                                  inst'span
                                  instExpr
                                  (EL'ObjVal clsVal)
                                  anno
                                  Nothing
                          analyzeBranch [(instKey, attrDef)]
                        _ -> do
                          !anno <- newTVar Nothing
                          let !attrDef =
                                EL'AttrDef
                                  instKey
                                  Nothing
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
                        ":>"
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
                        ">@"
                        prefixExpr@( ExprSrc
                                       ( InfixExpr
                                           "@<"
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
                el'AnalyzeExpr Nothing matchExpr $ \_result _eas ->
                  defExprAttrs
                    [ (AttrByName prefixName, prefixExpr),
                      (AttrByName suffixName, suffixExpr)
                    ]
                    analyzeBranch
            -- { match >@ suffix } -- prefix cut pattern
            [ StmtSrc
                ( ExprStmt
                    ( InfixExpr
                        ">@"
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
                el'AnalyzeExpr Nothing prefixExpr $ \_result _eas ->
                  defExprAttrs
                    [(AttrByName suffixName, suffixExpr)]
                    analyzeBranch
            -- { prefix @< match } -- suffix cut pattern
            [ StmtSrc
                ( ExprStmt
                    ( InfixExpr
                        "@<"
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
                el'AnalyzeExpr Nothing suffixExpr $ \_result _eas ->
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
              ] -> defDfAttrs odEmpty argSenders analyzeBranch
            --

            -- {( x:y:z:... )} -- pair pattern
            [ StmtSrc
                ( ExprStmt
                    (ParenExpr p1Expr@(ExprSrc (InfixExpr ":" _ _) _))
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
            --

            -- { term := value } -- definition pattern
            [ StmtSrc
                ( ExprStmt
                    ( InfixExpr
                        ":="
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
            el'AnalyzeExpr Nothing condExpr $
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
            el'AnalyzeExpr Nothing lhExpr $
              \_lhResult _eas -> analyzeBranch []
--

-- apk ctor
el'AnalyzeExpr _ (ExprSrc (ArgsPackExpr !argSndrs) _expr'span) !exit !eas =
  el'RunTx eas $ el'PackArgs argSndrs $ \ !apk -> el'ExitTx exit $ EL'Apk apk
--

-- list ctor
el'AnalyzeExpr _docCmt (ExprSrc (ListExpr !xs) _) !exit !eas = el'RunTx eas $
  el'AnalyzeExprs xs $ \ !vs !easDone ->
    el'Exit easDone exit . EL'List =<< newTVar vs
--

-- dict ctor
el'AnalyzeExpr _docCmt (ExprSrc (DictExpr !es) _) !exit !eas =
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
      el'AnalyzeExpr Nothing vx $ \ !v -> case dkx of
        LitDictKey !lit -> \ !easDone ->
          el'LiteralValue lit >>= \ !k ->
            el'RunTx easDone $ collectEntries ((k, v) : evs) rest
        AddrDictKey !kaddr -> el'AnalyzeExpr
          Nothing
          (ExprSrc (AttrExpr kaddr) noSrcRange)
          $ \ !k ->
            collectEntries ((k, v) : evs) rest
        ExprDictKey !kx -> el'AnalyzeExpr Nothing kx $ \ !k ->
          collectEntries ((k, v) : evs) rest
--

-- parenthesis
el'AnalyzeExpr !docCmt (ExprSrc (ParenExpr !x) _) !exit !eas =
  el'RunTx easPure $
    el'AnalyzeExpr docCmt x $ \ !val !easDone ->
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
el'AnalyzeExpr _docCmt (ExprSrc (LitExpr !lit) _expr'span) !exit !eas =
  el'Exit eas exit =<< el'LiteralValue lit
--

-- call making
el'AnalyzeExpr
  _docCmt
  xsrc@(ExprSrc (CallExpr !calleeExpr !argsSndr) _expr'span)
  !exit
  !eas = el'RunTx eas $
    el'AnalyzeExpr Nothing calleeExpr $ \_calleeVal -> el'PackArgs argsSndr $
      \_apk -> el'ExitTx exit $ EL'Expr xsrc
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
          Just (!msImporter, !resolvImporter) -> el'RunTx eas $
            el'LocateImportee msImporter litSpec $ \ !impResult _eas ->
              case impResult of
                Left !err -> do
                  el'LogDiag diags el'Error spec'span "err-import" err
                  el'Exit eas exit $ EL'Const nil
                Right !msImportee -> do
                  -- record as an attribute defined to reference the module
                  let defImpSym =
                        let !importeeDef =
                              EL'AttrDef
                                (AttrByName "this")
                                Nothing
                                "<module>"
                                zeroSrcRange
                                ( ExprSrc
                                    (AttrExpr (ThisRef noSrcRange))
                                    noSrcRange
                                )
                                (EL'ObjVal el'ModuleClass)
                                maoAnnotation
                                Nothing
                            !impDef =
                              EL'AttrDef
                                (AttrByName litSpec)
                                docCmt
                                "<import>"
                                spec'span
                                xsrc
                                (EL'External msImportee importeeDef)
                                maoAnnotation
                                Nothing
                         in recordCtxSym eac $ EL'DefSym impDef
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
                        defImpSym
                        el'Exit eas exit $ EL'ModuVal msImportee
                      EL'ModuResolving !resolving _acts -> \_ets -> do
                        -- record importer as a dependant
                        modifyTVar' (el'resolving'dependants resolving) $
                          Map.insert msImporter True
                        -- do import
                        !exps <- iopdSnapshot $ el'modu'exps'wip resolving
                        impIntoScope chkExp msImportee exps argsRcvr
                        defImpSym
                        el'Exit eas exit $ EL'ModuVal msImportee
        AttrExpr {} ->
          el'RunTx eas $ -- dynamic string or obj import
          -- TODO analyzetime string/object eval?
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
      !world = el'world eas
      !ets = el'ets eas
      !eac = el'context eas
      !swip = el'ctx'scope eac
      !pwip = el'ProcWIP swip
      !bwip = el'scope'branch'wip pwip
      diags = el'ctx'diags eac
      returnAsExpr = el'Exit eas exit $ EL'Expr xsrc

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
        EL'Artifacts ->
        ArgsReceiver ->
        STM ()
      impIntoScope !chkExp !srcModu !srcExps !asr = do
        let !srcArts = odMap (EL'External srcModu) srcExps
        case asr of
          WildReceiver -> forM_ (odToList srcArts) wildImp
          PackReceiver !ars -> go srcArts ars
          SingleReceiver !ar -> go srcArts [ar]
        -- record a region after this import, for current scope
        iopdSnapshot (el'branch'attrs'wip bwip)
          >>= modifyTVar' (el'branch'regions'wip bwip) . (:)
            . EL'RegionWIP (src'end expr'span)
        where
          !localTgt =
            if el'ctx'eff'defining eac
              then el'branch'effs'wip bwip
              else el'branch'attrs'wip bwip

          wildImp :: (AttrKey, EL'Value) -> STM ()
          wildImp (!k, !v) = do
            !artAnno <- newTVar =<< el'ResolveAnnotation swip k
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
              el'ResolveAttrAddr eas localAddr >>= \case
                Nothing ->
                  -- invalid attr addr, error should have been logged
                  go srcArts rest
                Just (AttrByName "_") -> go odEmpty rest -- explicit dropping
                Just !localKey -> do
                  !artAnno <- newTVar =<< el'ResolveAnnotation swip localKey
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
                el'ResolveAttrAddr eas localAddr >>= \case
                  Nothing ->
                    -- invalid attr addr, error should have been logged
                    go srcArts rest
                  Just !localKey ->
                    el'ResolveAttrAddr eas srcAddr >>= \case
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
                                  newTVar =<< el'ResolveAnnotation swip localKey
                                -- record as definition symbol of current scope
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
                                recordCtxSym eac $ EL'DefSym attrDef
                                -- register as local attribute
                                iopdInsert localKey attrDef localTgt
                                -- export it if specified so
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
           !expr'span
         )
  !exit
  !eas = do
    !instAttrs <- iopdEmpty
    !clsExts <- newTVar []
    !instExts <- newTVar []
    !clsExps <- iopdEmpty
    !instExps <- iopdEmpty
    !branchAttrs <- iopdEmpty
    !clsAttrs <- iopdEmpty
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
            clsExts
            clsExps
            clsScopes
            clsRegions
        !eacCls =
          EL'Context
            { el'ctx'scope =
                EL'DefineClass
                  ( EL'ClassWIP
                      instAttrs
                      clsExts
                      instExts
                      clsExps
                      instExps
                  )
                  pwip,
              el'ctx'outers = outerScope : el'ctx'outers eac,
              el'ctx'pure = False,
              el'ctx'exporting = False,
              el'ctx'eff'defining = False,
              el'ctx'symbols = el'ctx'symbols eac,
              el'ctx'diags = el'ctx'diags eac
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
                defDataField (AttrAddrSrc (NamedAttr "_") _) = go dfs rest
                defDataField dfAddr@(AttrAddrSrc _ df'name'span) =
                  el'ResolveAttrAddr eas dfAddr >>= \case
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
                        WildReceiver -- todo elaborate actual args
                        ( EL'Scope
                            cls'name'span
                            V.empty
                            V.empty
                        )
                    )
                )
                anno
                Nothing
            )

    -- define data fields as class attributes
    -- TODO this correct?
    case argsRcvr of
      -- a normal class
      WildReceiver -> pure ()
      -- a data class (ADT)
      SingleReceiver !ar -> defDataArts [ar]
      PackReceiver !ars -> defDataArts ars

    el'RunTx easCls $
      el'AnalyzeStmts [cls'body] $ \_ !easDone -> do
        let !eacDone = el'context easDone
            !swipDone = el'ctx'scope eacDone
            !pwipDone = el'ProcWIP swipDone
            !bwipDone = el'scope'branch'wip pwipDone
        !regions'wip <-
          fmap
            ( \(EL'RegionWIP !reg'start !reg'arts) ->
                EL'Region
                  (SrcRange reg'start (src'end body'span))
                  reg'arts
            )
            <$> readTVar (el'branch'regions'wip bwipDone)
        !innerScopes <- readTVar clsScopes
        !regions <-
          (regions'wip ++)
            <$> readTVar (el'scope'regions'wip pwipDone)

        !cls'exts <- readTVar clsExts
        !cls'exps <- iopdSnapshot clsExps
        !inst'attrs <- iopdSnapshot instAttrs
        !inst'exts <- readTVar instExts
        !inst'exps <- iopdSnapshot instExps
        let !cls'scope =
              EL'Scope
                { el'scope'span = body'span,
                  el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                  el'scope'regions = V.fromList $! reverse regions
                }
        -- record as an inner scope of outer scope
        modifyTVar' (el'scope'inner'scopes'wip outerProc) (cls'scope :)

        el'ResolveAttrAddr eas cls'name >>= \case
          Nothing -> el'Exit eas exit $ EL'Const nil
          Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
          Just !clsName -> do
            !clsAnno <- newTVar =<< el'ResolveAnnotation outerScope clsName
            let !mro = [] -- TODO C3 linearize cls'exts to get this
                !cls =
                  EL'Class
                    clsName
                    el'MetaClass
                    cls'exts
                    mro
                    cls'scope
                    (el'ScopeAttrs cls'scope)
                    cls'exps
                    inst'attrs
                    inst'exts
                    inst'exps
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
            -- record as definition symbol of outer scope
            recordCtxSym eac $ EL'DefSym clsDef
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
                      . EL'RegionWIP (src'end expr'span)

              when (el'ctx'exporting eac) $
                iopdInsert clsName clsDef $ el'scope'exps'wip outerProc

            -- return the class object value
            el'Exit eas exit clsVal
    where
      !eac = el'context eas
      !outerScope = el'ctx'scope eac
      !outerProc = el'ProcWIP outerScope
      !outerBranch = el'scope'branch'wip outerProc
      diags = el'ctx'diags eac
--

-- defining a method procedure
el'AnalyzeExpr !docCmt xsrc@(ExprSrc (MethodExpr !pd) _expr'span) !exit !eas =
  el'RunTx eas $ el'DefineMethod docCmt xsrc pd exit
el'AnalyzeExpr !docCmt xsrc@(ExprSrc (GeneratorExpr !pd) _expr'span) !exit !eas =
  el'RunTx eas $ el'DefineMethod docCmt xsrc pd exit
el'AnalyzeExpr !docCmt xsrc@(ExprSrc (InterpreterExpr !pd) _expr'span) !exit !eas =
  el'RunTx eas $ el'DefineMethod docCmt xsrc pd exit
el'AnalyzeExpr !docCmt xsrc@(ExprSrc (ProducerExpr !pd) _expr'span) !exit !eas =
  el'RunTx eas $ el'DefineMethod docCmt xsrc pd exit
-- defining an operator procedure
el'AnalyzeExpr
  !docCmt
  xsrc@( ExprSrc
           (OpDefiExpr _fixity _precedence _opSym !pd)
           _expr'span
         )
  !exit
  !eas =
    el'RunTx eas $ el'DefineMethod docCmt xsrc pd exit
el'AnalyzeExpr
  !docCmt
  xsrc@( ExprSrc
           (OpOvrdExpr _fixity _precedence _opSym !pd)
           _expr'span
         )
  !exit
  !eas =
    el'RunTx eas $ el'DefineMethod docCmt xsrc pd exit
--

-- defining a namespace
el'AnalyzeExpr _ (ExprSrc (NamespaceExpr HostDecl {} _) _) _exit _eas =
  error "bug: host ns decl"
el'AnalyzeExpr
  !docCmt
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
    !nsExts <- newTVar []
    !nsExps <- iopdEmpty
    !branchAttrs <- iopdEmpty
    !nsAttrs <- iopdEmpty
    !nsEffs <- iopdEmpty
    !nsAnnos <- iopdEmpty
    !branchRegions <- newTVar []
    !nsScopes <- newTVar []
    !nsRegions <- newTVar []
    let !bwip =
          EL'BranchWIP
            branchAttrs
            nsEffs
            nsAnnos
            branchRegions
        !pwip =
          EL'ProcWIP
            bwip
            nsAttrs
            nsExts
            nsExps
            nsScopes
            nsRegions
        !eacNs =
          EL'Context
            { el'ctx'scope =
                EL'InitObject (EL'ObjectWIP nsAttrs nsExts nsExps) pwip,
              el'ctx'outers = outerScope : el'ctx'outers eac,
              el'ctx'pure = False,
              el'ctx'exporting = False,
              el'ctx'eff'defining = False,
              el'ctx'symbols = el'ctx'symbols eac,
              el'ctx'diags = el'ctx'diags eac
            }
        !easNs = eas {el'context = eacNs}

        -- define artifacts from arguments for a namespace
        defNsArgs ::
          [ArgSender] -> ([(AttrKey, EL'AttrDef)] -> STM ()) -> STM ()
        defNsArgs !aps !nsaExit = go [] aps
          where
            go :: [(AttrKey, EL'AttrDef)] -> [ArgSender] -> STM ()
            go !argArts [] = nsaExit $ reverse argArts
            go !argArts (argSndr : rest) = case argSndr of
              SendKwArg argAddr@(AttrAddrSrc _ !arg'name'span) !argExpr ->
                el'ResolveAttrAddr eas argAddr >>= \case
                  Nothing -> go argArts rest
                  Just !argKey -> el'RunTx eas $
                    el'AnalyzeExpr docCmt argExpr $ \ !argVal _eas -> do
                      !argAnno <- newTVar Nothing
                      go
                        ( ( argKey,
                            EL'AttrDef
                              argKey
                              Nothing
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

    defNsArgs argsPkr $ \ !argArts -> do
      iopdUpdate argArts nsAttrs
      -- record a region starting from beginning of the body
      iopdSnapshot nsAttrs
        >>= modifyTVar' branchRegions . (:)
          . EL'RegionWIP (src'start body'span)
      el'RunTx easNs $
        el'AnalyzeStmts [ns'body] $ \_ !easDone -> do
          let !eacDone = el'context easDone
              !swipDone = el'ctx'scope eacDone
              !pwipDone = el'ProcWIP swipDone
              !bwipDone = el'scope'branch'wip pwipDone
          !regions'wip <-
            fmap
              ( \(EL'RegionWIP !reg'start !reg'arts) ->
                  EL'Region
                    (SrcRange reg'start (src'end body'span))
                    reg'arts
              )
              <$> readTVar (el'branch'regions'wip bwipDone)

          -- update annotations for arguments from body
          forM_ argArts $ \(!argName, !argDef) ->
            iopdLookup argName nsAnnos >>= \case
              Nothing -> pure ()
              Just !anno ->
                writeTVar (el'attr'def'anno argDef) $ Just anno
          --

          !ns'attrs <- iopdSnapshot nsAttrs
          !ns'exts <- readTVar nsExts
          !ns'exps <- iopdSnapshot nsExps
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

          el'ResolveAttrAddr eas ns'name >>= \case
            Nothing -> el'Exit eas exit $ EL'Const nil
            Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
            Just !nsName -> do
              !nsAnno <- newTVar =<< el'ResolveAnnotation outerScope nsName
              let !nsCls =
                    el'NamespaceClass
                      { el'class'name = nsName,
                        el'class'scope = ns'scope,
                        el'inst'attrs = ns'attrs,
                        el'inst'exts = ns'exts,
                        el'inst'exps = ns'exps
                      }
                  !nsVal = EL'ObjVal nsCls
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
              recordCtxSym eac $ EL'DefSym nsDef
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
                        . EL'RegionWIP (src'end expr'span)

                when (el'ctx'exporting eac) $
                  iopdInsert nsName nsDef $ el'scope'exps'wip outerProc

              -- return the namespace object value
              el'Exit eas exit nsVal
    where
      !eac = el'context eas
      !outerScope = el'ctx'scope eac
      !outerProc = el'ProcWIP outerScope
      !outerBranch = el'scope'branch'wip outerProc
      diags = el'ctx'diags eac
--

-- scoped block
el'AnalyzeExpr _docCmt (ExprSrc (ScopedBlockExpr !stmts) !blk'span) !exit !eas =
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
        !regions'wip <-
          fmap
            ( \(EL'RegionWIP !reg'start !reg'arts) ->
                EL'Region
                  (SrcRange reg'start (src'end blk'span))
                  reg'arts
            )
            <$> readTVar (el'branch'regions'wip bwipDone)
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
el'AnalyzeExpr _docCmt (ExprSrc (VoidExpr !expr) _expr'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing expr $ const $ el'ExitTx exit $ EL'Const nil
--

-- ai operator
el'AnalyzeExpr _docCmt (ExprSrc (AtoIsoExpr !expr) _expr'span) !exit !eas =
  el'RunTx eas $ el'AnalyzeExpr Nothing expr exit
--

-- prefix operator
el'AnalyzeExpr _docCmt x@(ExprSrc (PrefixExpr _ !expr) _expr'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing expr $ const $ el'ExitTx exit $ EL'Expr x
--

-- if
el'AnalyzeExpr
  _docCmt
  x@(ExprSrc (IfExpr !cond !cseq !maybeAlt) _expr'span)
  !exit
  !eas =
    -- TODO use branch in cseq/alt, close when it evals to `return`
    el'RunTx eas $
      el'AnalyzeExpr Nothing cond $
        const $
          el'AnalyzeStmt cseq $
            const $ case maybeAlt of
              Nothing -> el'ExitTx exit $ EL'Expr x
              Just !alt ->
                el'AnalyzeStmt alt $ const $ el'ExitTx exit $ EL'Expr x
--

-- case-of
el'AnalyzeExpr _docCmt x@(ExprSrc (CaseExpr !tgt !bs) !expr'span) !exit !eas0 =
  el'RunTx eas0 $
    el'AnalyzeExpr Nothing tgt $
      const $
        el'AnalyzeExpr Nothing bs $ \_result !eas -> do
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
              (EL'RegionWIP (src'end expr'span) attrs :)

          el'Exit eas exit $ EL'Expr x
--

-- for-from-do
el'AnalyzeExpr
  _docCmt
  x@(ExprSrc (ForExpr !asr !it body@(StmtSrc _ !body'span)) _expr'span)
  !exit
  !eas = do
    !loopArts <- case asr of
      WildReceiver -> return []
      PackReceiver !ars -> defLoopArts ars
      SingleReceiver !ar -> defLoopArts [ar]
    unless (null loopArts) $ do
      iopdUpdate loopArts $ el'scope'attrs'wip pwip
      iopdUpdate loopArts attrs
      -- record a region before the loop body for current scope
      iopdSnapshot attrs
        >>= modifyTVar' (el'branch'regions'wip bwip) . (:)
          . EL'RegionWIP (src'start body'span)

    el'RunTx eas $
      el'AnalyzeExpr Nothing it $
        const $
          el'AnalyzeStmt body $ \_result _eas -> do
            -- record a new region following this for-from-do loop
            -- TODO check whether new attrs actually added, don't record if not
            !scope'attrs <- iopdSnapshot (el'scope'attrs'wip pwip)
            modifyTVar'
              (el'branch'regions'wip bwip)
              (EL'RegionWIP (src'end body'span) scope'attrs :)

            el'Exit eas exit $ EL'Expr x
    where
      !eac = el'context eas
      !swip = el'ctx'scope eac
      !pwip = el'ProcWIP swip
      !bwip = el'scope'branch'wip pwip
      !attrs = el'branch'attrs'wip bwip
      !annos = el'branch'annos'wip bwip

      -- define artifacts from loop receivers
      defLoopArts :: [ArgReceiver] -> STM [(AttrKey, EL'AttrDef)]
      defLoopArts !ars = go [] ars
        where
          go ::
            [(AttrKey, EL'AttrDef)] ->
            [ArgReceiver] ->
            STM [(AttrKey, EL'AttrDef)]
          go !args [] = return $ reverse args
          go !args (ar : rest) = case ar of
            RecvArg !argAddr !maybeRename !maybeDef -> case maybeRename of
              Nothing -> defLoopArt argAddr maybeDef
              Just (DirectRef !argAddr') -> defLoopArt argAddr' Nothing
              Just _otherRename -> go args rest -- TODO elaborate?
            RecvRestPkArgs !argAddr -> defLoopArt argAddr Nothing
            RecvRestKwArgs !argAddr -> defLoopArt argAddr Nothing
            RecvRestPosArgs !argAddr -> defLoopArt argAddr Nothing
            where
              defLoopArt (AttrAddrSrc (NamedAttr "_") _) _ = go args rest
              defLoopArt argAddr@(AttrAddrSrc _ arg'name'span) !knownExpr =
                el'ResolveAttrAddr eas argAddr >>= \case
                  Nothing -> go args rest
                  Just !argKey ->
                    iopdLookup argKey annos >>= newTVar >>= \ !anno ->
                      go
                        ( ( argKey,
                            EL'AttrDef
                              argKey
                              Nothing
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
--

-- yield
el'AnalyzeExpr _docCmt x@(ExprSrc (YieldExpr !expr) _expr'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing expr $ const $ el'ExitTx exit $ EL'Expr x
--

-- indexing
el'AnalyzeExpr _docCmt x@(ExprSrc (IndexExpr !idx !tgt) _expr'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing tgt $
      const $ el'AnalyzeExpr Nothing idx $ const $ el'ExitTx exit $ EL'Expr x
--

-- default
el'AnalyzeExpr _docCmt x@(ExprSrc (DefaultExpr !expr) _expr'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing expr $ const $ el'ExitTx exit $ EL'Expr x
--

-- interpolated expr
-- todo should this reachable ? as the original expr in ExprWithSrc won't be
-- analyzed.
el'AnalyzeExpr _docCmt (ExprSrc (IntplExpr !expr) _expr'span) !exit !eas =
  el'RunTx eas $ el'AnalyzeExpr Nothing expr exit
--

-- expr with source (including interpolations)
el'AnalyzeExpr
  _docCmt
  (ExprSrc (ExprWithSrc !expr !segs) _expr'span)
  !exit
  !eas = go segs
    where
      go [] = el'Exit eas exit $ EL'Expr expr
      go (SrcSeg {} : rest) = go rest
      go (IntplSeg !ix : rest) = el'RunTx eas $
        el'AnalyzeExpr Nothing ix $ \_ _eas -> go rest
--

-- perform
-- todo analyze dynamic scoped effects
el'AnalyzeExpr _docCmt x@(ExprSrc (PerformExpr _addr) _expr'span) !exit !eas =
  el'Exit eas exit $ EL'Expr x
--

-- behave
-- todo analyze dynamic scoped effects
el'AnalyzeExpr _docCmt x@(ExprSrc (BehaveExpr _addr) _expr'span) !exit !eas =
  el'Exit eas exit $ EL'Expr x
--

-- symbol definition
el'AnalyzeExpr !docCmt xsrc@(ExprSrc (SymbolExpr !attr) !expr'span) !exit !eas =
  do
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

    -- record as definition symbol of current scope
    recordCtxSym eac $ EL'DefSym symDef

    -- record as artifact of current scope
    unless (el'ctx'pure eac) $ do
      let !attrs = el'branch'attrs'wip bwip
      iopdInsert symName symDef $ el'scope'attrs'wip pwip
      iopdInsert symName symDef attrs
      -- record a region after this definition for current scope
      iopdSnapshot attrs
        >>= modifyTVar' (el'branch'regions'wip bwip) . (:)
          . EL'RegionWIP (src'end expr'span)

      when (el'ctx'exporting eac) $
        iopdInsert symName symDef $ el'scope'exps'wip pwip

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
el'AnalyzeExpr _docCmt !xsrc !exit !eas = el'Exit eas exit $ EL'Expr xsrc

-- | define a method procedure
el'DefineMethod ::
  Maybe DocComment ->
  ExprSrc ->
  ProcDecl ->
  EL'Analysis EL'Value
el'DefineMethod _ _ HostDecl {} _exit _eas =
  error "bug: host method decl"
el'DefineMethod
  !docCmt
  !xsrc
  ( ProcDecl
      mth'name@(AttrAddrSrc _mth'name'addr !mth'name'span)
      !argsRcvr
      mth'body@(StmtSrc _body'stmt !body'span)
      _mth'proc'loc
    )
  !exit
  !eas = do
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
                el'scope'exts'wip = el'inst'exts'wip cwip,
                el'scope'exps'wip = el'inst'exps'wip cwip,
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
              el'ctx'symbols = el'ctx'symbols eac,
              el'ctx'diags = el'ctx'diags eac
            }
        !easMth = eas {el'context = eacMth}

    !argArts <- case argsRcvr of
      WildReceiver -> return []
      PackReceiver !ars -> defArgArts ars
      SingleReceiver !ar -> defArgArts [ar]
    iopdUpdate argArts mthAttrs

    el'RunTx easMth $
      el'AnalyzeStmts [mth'body] $ \_ !easDone -> do
        let !eacDone = el'context easDone
            !swipDone = el'ctx'scope eacDone
            !pwipDone = el'ProcWIP swipDone
            !bwipDone = el'scope'branch'wip pwipDone
        !regions'wip <-
          fmap
            ( \(EL'RegionWIP !reg'start !reg'arts) ->
                EL'Region
                  (SrcRange reg'start (src'end body'span))
                  reg'arts
            )
            <$> readTVar (el'branch'regions'wip bwipDone)
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

        el'ResolveAttrAddr eas mth'name >>= \case
          Nothing -> el'Exit eas exit $ EL'Const nil
          Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
          Just !mthName -> do
            !mthAnno <- newTVar =<< el'ResolveAnnotation outerScope mthName
            let -- TODO for sake of parameter hints in IDE
                -- - elide 1st `callerScope` for interpreter and 3-arg operator
                -- - supplement `outlet` for producer if omitted
                !mth = EL'Proc mthName argsRcvr mth'scope
                !mthVal = EL'ProcVal mth
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
            recordCtxSym eac $ EL'DefSym mthDef
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
                      . EL'RegionWIP (src'end body'span)

              when (el'ctx'exporting eac) $
                iopdInsert mthName mthDef $ el'scope'exps'wip outerProc

            -- return the procedure object value
            el'Exit eas exit mthVal
    where
      !eac = el'context eas
      !outerScope = el'ctx'scope eac
      !outerProc = el'ProcWIP outerScope
      !outerBranch = el'scope'branch'wip outerProc
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
              defArgArt (AttrAddrSrc (NamedAttr "_") _) _ = go args rest
              defArgArt argAddr@(AttrAddrSrc _ arg'name'span) !knownExpr =
                el'ResolveAttrAddr eas argAddr >>= \case
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
        goDef (PackReceiver [])
      Right !argsRcvr -> goDef argsRcvr
    where
      !eac = el'context eas
      !outerScope = el'ctx'scope eac
      !outerProc = el'ProcWIP outerScope
      !outerBranch = el'scope'branch'wip outerProc
      diags = el'ctx'diags eac

      -- define artifacts from arguments for an arrow procedure
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
              defArgArt (AttrAddrSrc (NamedAttr "_") _) _ = go args rest
              defArgArt argAddr@(AttrAddrSrc _ arg'name'span) !knownExpr =
                el'ResolveAttrAddr eas argAddr >>= \case
                  Nothing -> go args rest
                  Just !argKey ->
                    newTVar Nothing >>= \ !anno ->
                      go
                        ( ( argKey,
                            EL'AttrDef
                              argKey
                              Nothing
                              "<arrow-argument>"
                              arg'name'span
                              lhExpr
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

      goDef :: ArgsReceiver -> STM ()
      goDef !argsRcvr = do
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
                    el'scope'exts'wip = el'inst'exts'wip cwip,
                    el'scope'exps'wip = el'inst'exps'wip cwip,
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
                  el'ctx'symbols = el'ctx'symbols eac,
                  el'ctx'diags = el'ctx'diags eac
                }
            !easMth = eas {el'context = eacMth}

        !argArts <- case argsRcvr of
          WildReceiver -> return []
          PackReceiver !ars -> defArgArts ars
          SingleReceiver !ar -> defArgArts [ar]
        iopdUpdate argArts mthAttrs

        el'RunTx easMth $
          el'AnalyzeExpr Nothing rhExpr $ \_ !easDone -> do
            let !eacDone = el'context easDone
                !swipDone = el'ctx'scope eacDone
                !pwipDone = el'ProcWIP swipDone
                !bwipDone = el'scope'branch'wip pwipDone
            !regions'wip <-
              fmap
                ( \(EL'RegionWIP !reg'start !reg'arts) ->
                    EL'Region
                      (SrcRange reg'start (src'end body'span))
                      reg'arts
                )
                <$> readTVar (el'branch'regions'wip bwipDone)
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
                -- TODO for sake of parameter hints in IDE
                -- - elide 1st `callerScope` for interpreter and 3-arg operator
                -- - supplement `outlet` for producer if omitted
                !mth = EL'Proc mthName argsRcvr mth'scope
                !mthVal = EL'ProcVal mth
            --

            -- record as an inner scope of outer scope
            modifyTVar' (el'scope'inner'scopes'wip outerProc) (mth'scope :)

            -- return the procedure object value
            el'Exit eas exit mthVal

--
