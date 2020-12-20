module Language.Edh.Meta.Analyze where

import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import qualified Data.ByteString as B
import Data.Dynamic
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import qualified Data.Map.Strict as TreeMap
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
el'WalkResolutionDiags !ms !walker =
  tryReadTMVar reso >>= \case
    Nothing -> return ()
    Just (EL'ModuResolving !resolving _acts) -> do
      walker ms =<< readTVar (el'resolving'diags resolving)
      walkDeps . Map.toList =<< readTVar (el'resolving'dependants resolving)
    Just (EL'ModuResolved !resolved) -> do
      walker ms $ el'resolution'diags resolved
      walkDeps $ Map.toList $ el'modu'dependencies resolved
  where
    !reso = el'modu'resolution ms
    walkDeps :: [(EL'ModuSlot, Bool)] -> STM ()
    walkDeps [] = return ()
    walkDeps ((!dep, !hold) : rest) = do
      when hold $ el'WalkResolutionDiags dep walker
      walkDeps rest

-- | walk through all diagnostics for a module, including all its dependencies
el'WalkParsingDiags ::
  EL'ModuSlot ->
  (EL'ModuSlot -> [EL'Diagnostic] -> STM ()) ->
  STM ()
el'WalkParsingDiags !ms !walker = do
  tryReadTMVar pars >>= \case
    Just (EL'ModuParsed !parsed) -> walker ms $ el'parsing'diags parsed
    _ -> return ()
  tryReadTMVar reso >>= \case
    Nothing -> return ()
    Just (EL'ModuResolving !resolving _resolvedVar) ->
      walkDeps . Map.toList =<< readTVar (el'modu'dependencies'wip resolving)
    Just (EL'ModuResolved !resolved) ->
      walkDeps $ Map.toList $ el'modu'dependencies resolved
  where
    !pars = el'modu'parsing ms
    !reso = el'modu'resolution ms
    walkDeps :: [(EL'ModuSlot, Bool)] -> STM ()
    walkDeps [] = return ()
    walkDeps ((!dep, !hold) : rest) = do
      when hold $ el'WalkParsingDiags dep walker
      walkDeps rest

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
                    odEmpty
                    odEmpty
                    V.empty
                )
                odEmpty
                Map.empty
                [ el'Diag
                    el'Error
                    noSrcRange
                    "resolve-err"
                    exDesc
                ]
                (el'resolving'dependants resolving)

resolveParsedModule ::
  EL'World ->
  EL'ModuSlot ->
  EL'ResolvingModu ->
  [StmtSrc] ->
  EdhProc EL'ResolvedModule
resolveParsedModule !world !ms !resolving !body !exit !ets = do
  !moduAttrs <- iopdEmpty
  !moduEffs <- iopdEmpty
  !moduAnnos <- iopdEmpty
  !moduScopes <- newTVar []
  !moduRegions <- newTVar []
  !moduSyms <- newTVar TreeMap.empty
  let !pwip =
        EL'AnaProc
          (el'modu'exts'wip resolving)
          (el'modu'exps'wip resolving)
          moduAttrs
          moduEffs
          moduAnnos
          moduScopes
          moduRegions
          moduSyms
      !eac =
        EL'Context
          { el'ctx'scope = EL'ModuWIP ms resolving pwip,
            el'ctx'outers = [],
            el'ctx'pure = False,
            el'ctx'exporting = False,
            el'ctx'eff'defining = False,
            el'ctx'diags = el'resolving'diags resolving
          }
      !eas =
        EL'AnalysisState
          { el'world = world,
            el'context = eac,
            el'ets = ets
          }

  el'RunTx eas $
    el'AnalyzeStmts body $ \_ _eas -> do
      !diags <- readTVar $ el'resolving'diags resolving
      !moduExps <- iopdSnapshot $ el'modu'exps'wip resolving
      !dependencies <- readTVar $ el'modu'dependencies'wip resolving
      !scope'attrs <- iopdSnapshot moduAttrs
      !scope'effs <- iopdSnapshot moduEffs
      !innerScopes <- readTVar moduScopes
      !regions <- readTVar moduRegions
      !scope'symbols <- readTVar moduSyms
      let !el'scope =
            EL'Scope
              { el'scope'span = SrcRange beginningSrcPos moduEnd,
                el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                el'scope'regions = V.fromList $! reverse regions,
                el'scope'attrs = scope'attrs,
                el'scope'effs = scope'effs,
                el'scope'symbols =
                  V.fromList $ snd <$> TreeMap.toAscList scope'symbols
              }
      exitEdh ets exit $
        EL'ResolvedModule
          el'scope
          moduExps
          dependencies
          (reverse diags)
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
el'PackArgs !argSndrs !exit !eas =
  el'RunTx easPure $ collectArgs [] [] argSndrs
  where
    !eac = el'context eas
    !easPure = eas {el'context = eac {el'ctx'pure = True}}

    collectArgs :: [EL'Value] -> [(AttrKey, EL'Value)] -> [ArgSender] -> EL'Tx
    collectArgs !args !kwargs [] = \_eas ->
      el'Exit eas exit $ EL'ArgsPack (reverse args) $ odFromList $ reverse kwargs
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
      SendKwArg !argAddr !ax -> \_eas ->
        el'ResolveAttrAddr eas argAddr >>= \case
          Nothing -> el'RunTx easPure $ collectArgs args kwargs rest
          Just !argKey -> el'RunTx easPure $
            el'AnalyzeExpr Nothing ax $ \ !argVal ->
              collectArgs args ((argKey, argVal) : kwargs) rest

-- * statement analysis

-- | a sequence of statements
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

            -- record a region after this let statement, for current scope
            iopdSnapshot (el'scope'attrs'wip pwip)
              >>= modifyTVar' (el'scope'regions'wip pwip) . (:)
                . EL'Region (src'end stmt'span)

            el'Exit eas exit $ EL'Const nil
    where
      {- HLINT ignore "Reduce duplication" -}
      !eac = el'context eas
      diags = el'ctx'diags eac
      !swip = el'ctx'scope eac
      !pwip = el'ProcWIP swip

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
          iopdSnapshot (el'scope'attrs'wip pwip)
            >>= modifyTVar' (el'scope'regions'wip pwip) . (:)
              . EL'Region (src'end stmt'span)

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
                          $ el'AnalyzeExpr Nothing defExpr $ \ !defVal _eas -> do
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
        !attrAnno <- newTVar =<< iopdLookup attrKey (el'scope'annos'wip pwip)
        !prevDef <-
          iopdLookup attrKey $
            if el'ctx'eff'defining eac
              then el'scope'effs'wip pwip
              else el'scope'attrs'wip pwip
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
        if el'ctx'eff'defining eac
          then do
            let !effs = el'scope'effs'wip pwip
            case attrVal of
              EL'Const EdhNil -> iopdDelete attrKey effs
              _ -> iopdInsert attrKey attrDef effs
          else do
            let !attrs = el'scope'attrs'wip pwip
            case attrVal of
              EL'Const EdhNil -> iopdDelete attrKey attrs
              _ -> do
                iopdInsert attrKey attrDef attrs
                -- record as definition symbol of current scope
                recordScopeSymbol pwip $ EL'DefSym attrDef
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

    scope = el'ctx'scope eac
    pwip = el'ProcWIP scope
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
      const $
        el'AnalyzeStmt body $
          const $ el'ExitTx exit $ EL'Const nil
--

-- throw
el'AnalyzeStmt (StmtSrc (ThrowStmt !expr) _stmt'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing expr $ const $ el'ExitTx exit $ EL'Const nil
--

-- return
el'AnalyzeStmt (StmtSrc (ReturnStmt !expr) _stmt'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing expr $ const $ el'ExitTx exit $ EL'Const nil
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
  TypeLiteral !v -> return $ EL'Const (EdhType v)
  SinkCtor -> EL'Const . EdhSink <$> newEventSink
  ValueLiteral !v -> return $ EL'Const v

-- | analyze an expression in context
el'AnalyzeExpr :: Maybe DocComment -> ExprSrc -> EL'Analysis EL'Value
--

-- block
el'AnalyzeExpr _docCmt (ExprSrc (BlockExpr !stmts) _blk'span) !exit !eas =
  el'RunTx eas $ el'AnalyzeStmts stmts exit
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
      Nothing -> do
        el'LogDiag
          diags
          el'Error
          addr'span
          "bad-ref"
          "bad attribute addressor"
        returnAsExpr
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
            recordScopeSymbol pwip $ EL'RefSym attrRef

            el'Exit eas exit $ el'attr'def'value attrDef
    where
      !eac = el'context eas
      diags = el'ctx'diags eac
      !swip = el'ctx'scope eac
      !pwip = el'ProcWIP swip
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
    el'AnalyzeExpr Nothing tgtExpr $ \ !tgtVal _eas -> case tgtVal of
      EL'ObjVal !obj ->
        el'ResolveAttrAddr eas addr >>= \case
          Nothing -> returnAsExpr
          Just !refKey -> case odLookup refKey (el'obj'attrs obj) of
            Nothing -> do
              el'LogDiag
                diags
                el'Error
                addr'span
                "no-such-attr"
                "no such attribute"
              returnAsExpr
            Just !attrDef -> do
              -- record as referencing symbol of outer scope
              let !attrRef = EL'AttrRef addr attrDef
              recordScopeSymbol pwip $ EL'RefSym attrRef

              el'Exit eas exit $ el'attr'def'value attrDef
      EL'ClsVal !cls ->
        el'ResolveAttrAddr eas addr >>= \case
          Nothing -> returnAsExpr
          Just !refKey -> case odLookup
            refKey
            (el'scope'attrs $ el'class'scope cls) of
            Nothing -> do
              el'LogDiag
                diags
                el'Error
                addr'span
                "no-such-attr"
                "no such attribute"
              returnAsExpr
            Just !attrDef -> do
              -- record as referencing symbol of outer scope
              let !attrRef = EL'AttrRef addr attrDef
              recordScopeSymbol pwip $ EL'RefSym attrRef

              el'Exit eas exit $ el'attr'def'value attrDef
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
      !swip = el'ctx'scope eac
      !pwip = el'ProcWIP swip
      returnAsExpr = el'Exit eas exit $ EL'Expr xsrc
--

-- infix operator application
el'AnalyzeExpr
  !docCmt
  xsrc@( ExprSrc
           (InfixExpr !opSym lhExpr@(ExprSrc !lhx _lh'span) !rhExpr)
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
    "->" ->
      let goAnalyzeRHS :: EL'Tx
          goAnalyzeRHS = el'AnalyzeExpr Nothing rhExpr $ \_ _eas -> returnAsExpr

          handlePattern :: Expr -> EL'Tx
          handlePattern = \case
            -- curly braces at lhs means a pattern
            -- TODO analyze attr definitions in the patterns
            DictExpr {} -> goAnalyzeRHS
            BlockExpr {} -> goAnalyzeRHS
            -- not a pattern, value match
            _ -> el'AnalyzeExpr Nothing lhExpr $ const goAnalyzeRHS
       in el'RunTx eas $ case lhx of
            -- wild match
            AttrExpr (DirectRef (AttrAddrSrc (NamedAttr "_") _)) ->
              goAnalyzeRHS
            -- guarded, pattern or value match
            InfixExpr "|" (ExprSrc !matchExpr _) !guardExpr ->
              el'AnalyzeExpr Nothing guardExpr $ \_ -> handlePattern matchExpr
            _ -> handlePattern lhx
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
          Nothing -> returnAsExpr
          Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
          Just !attrKey -> do
            let !attrAnno = EL'AttrAnno rhExpr docCmt
            iopdInsert attrKey attrAnno (el'scope'annos'wip pwip)
            el'Exit eas exit $ EL'Const nil
      ExprSrc _ !bad'anno'span -> do
        el'LogDiag
          diags
          el'Warning
          bad'anno'span
          "bad-anno"
          "bad annotation"
        returnAsExpr
    --

    -- left-dropping annotation
    "!" -> el'RunTx eas $ el'AnalyzeExpr docCmt rhExpr exit
    --

    -- TODO special treatment of ($) (|) (&) etc. ?

    -- other operations without special treatment
    _ -> el'RunTx easPure $
      el'AnalyzeExpr Nothing lhExpr $ \_lhVal ->
        el'AnalyzeExpr Nothing rhExpr $ \_rhVal _eas -> returnAsExpr
        --

        --
    where
      !eac = el'context eas
      diags = el'ctx'diags eac
      !swip = el'ctx'scope eac
      !pwip = el'ProcWIP swip
      returnAsExpr = el'Exit eas exit $ EL'Expr xsrc

      easPure = eas {el'context = eac {el'ctx'pure = True}}

      doCmp = el'RunTx easPure $
        el'AnalyzeExpr Nothing lhExpr $ \_lhVal ->
          el'AnalyzeExpr Nothing rhExpr $ \_rhVal _eas -> returnAsExpr

      doAssign = el'RunTx easPure $
        el'AnalyzeExpr Nothing rhExpr $ \ !rhVal _eas -> do
          case lhExpr of
            ExprSrc (AttrExpr (DirectRef addr@(AttrAddrSrc _ !addr'span))) _ ->
              el'ResolveAttrAddr eas addr >>= \case
                Nothing -> returnAsExpr
                Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
                Just !attrKey -> do
                  !attrAnno <-
                    newTVar =<< iopdLookup attrKey (el'scope'annos'wip pwip)
                  !prevDef <-
                    iopdLookup attrKey $
                      if el'ctx'eff'defining eac
                        then el'scope'effs'wip pwip
                        else el'scope'attrs'wip pwip
                  let !attrDef =
                        EL'AttrDef
                          attrKey
                          docCmt
                          opSym
                          addr'span
                          xsrc
                          rhVal
                          attrAnno
                          prevDef

                  -- record as artifact of current scope
                  unless (el'ctx'pure eac) $ do
                    if el'ctx'eff'defining eac
                      then do
                        let !effs = el'scope'effs'wip pwip
                        case rhVal of
                          EL'Const EdhNil -> iopdDelete attrKey effs
                          _ -> iopdInsert attrKey attrDef effs
                      else do
                        let !attrs = el'scope'attrs'wip pwip
                        case rhVal of
                          EL'Const EdhNil -> do
                            iopdDelete attrKey attrs
                            iopdSnapshot attrs
                              >>= modifyTVar' (el'scope'regions'wip pwip) . (:)
                                . EL'Region (src'end expr'span)
                          _ -> do
                            iopdInsert attrKey attrDef attrs
                            -- record as definition symbol of current scope
                            recordScopeSymbol pwip $ EL'DefSym attrDef
                            case prevDef of
                              -- assignment created a new attr, record a region
                              -- after this assignment expr for current scope
                              Nothing ->
                                iopdSnapshot attrs
                                  >>= modifyTVar' (el'scope'regions'wip pwip)
                                    . (:)
                                    . EL'Region (src'end expr'span)
                              _ -> pure ()
                    when (el'ctx'exporting eac) $
                      iopdInsert attrKey attrDef $ el'scope'exps'wip pwip
                  --

                  if "=" == opSym || ":=" == opSym
                    then el'Exit eas exit rhVal
                    else returnAsExpr
            ExprSrc
              (AttrExpr (IndirectRef !tgtExpr !addr))
              _expr'span -> el'RunTx easPure $
                el'AnalyzeExpr Nothing tgtExpr $ \_tgtVal _eas ->
                  -- TODO add to lh obj attrs for (=) ?
                  --      other cases ?
                  el'ResolveAttrAddr eas addr >> returnAsExpr
            ExprSrc
              (IndexExpr !idxExpr !tgtExpr)
              _expr'span ->
                el'RunTx easPure $
                  el'AnalyzeExpr Nothing idxExpr $ \_idxVal ->
                    el'AnalyzeExpr Nothing tgtExpr $ \_tgtVal _eas ->
                      returnAsExpr
            ExprSrc _ !bad'assign'tgt'span -> do
              el'LogDiag
                diags
                el'Error
                bad'assign'tgt'span
                "bad-assign-target"
                "bad assignment target"
              returnAsExpr
--

-- apk ctor
el'AnalyzeExpr _ (ExprSrc (ArgsPackExpr !argSndrs) _expr'span) !exit !eas =
  el'RunTx eas $
    el'PackArgs argSndrs $ \ !apk -> el'ExitTx exit $ EL'Apk apk
--

-- list ctor
el'AnalyzeExpr _docCmt (ExprSrc (ListExpr !xs) _) !exit !eas =
  el'RunTx easPure $ collectValues [] xs
  where
    !eac = el'context eas
    !easPure = eas {el'context = eac {el'ctx'pure = True}}

    collectValues :: [EL'Value] -> [ExprSrc] -> EL'Tx
    collectValues !vs [] = \_eas ->
      el'Exit eas exit . EL'List =<< (newTVar $! reverse vs)
    collectValues !vs (x : rest) = el'AnalyzeExpr Nothing x $ \ !v ->
      collectValues (v : vs) rest
--

-- dict ctor
el'AnalyzeExpr _docCmt (ExprSrc (DictExpr !es) _) !exit !eas =
  el'RunTx easPure $ collectEntries [] es
  where
    !eac = el'context eas
    !easPure = eas {el'context = eac {el'ctx'pure = True}}

    collectEntries ::
      [(EL'Value, EL'Value)] ->
      [(DictKeyExpr, ExprSrc)] ->
      EL'Tx
    collectEntries !evs [] = \_eas ->
      el'Exit eas exit . EL'Dict =<< (newTVar $! reverse evs)
    collectEntries !evs ((!dkx, !vx) : rest) =
      el'AnalyzeExpr Nothing vx $ \ !v -> case dkx of
        LitDictKey !lit -> \_eas ->
          el'LiteralValue lit >>= \ !k ->
            el'RunTx easPure $ collectEntries ((k, v) : evs) rest
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
    el'AnalyzeExpr docCmt x $ \ !val _eas -> el'Exit eas exit val
  where
    !eac = el'context eas
    !easPure = eas {el'context = eac {el'ctx'pure = True}}
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
                  -- record as an attribute defined to reference the module,
                  -- this have to be performed later than the importing of
                  -- artifacts, to preserve symbol order in the source
                  let defImpSym =
                        let !importeeDef =
                              EL'AttrDef
                                (AttrByName "this")
                                Nothing
                                "<module>"
                                zeroSrcRange
                                (ExprSrc (AttrExpr ThisRef) noSrcRange)
                                ( EL'ObjVal
                                    ( EL'Object
                                        el'ModuleClass
                                        []
                                        odEmpty
                                        odEmpty
                                    )
                                )
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
                         in recordScopeSymbol pwip $ EL'DefSym impDef
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
      swip = el'ctx'scope eac
      pwip = el'ProcWIP swip
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
        iopdSnapshot (el'scope'attrs'wip pwip)
          >>= modifyTVar' (el'scope'regions'wip pwip) . (:)
            . EL'Region (src'end expr'span)
        where
          !localTgt =
            if el'ctx'eff'defining eac
              then el'scope'effs'wip pwip
              else el'scope'attrs'wip pwip

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
                                recordScopeSymbol pwip $ EL'DefSym attrDef
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
    !clsExts <- newTVar []
    !instExts <- newTVar []
    !clsExps <- iopdEmpty
    !instExps <- iopdEmpty
    !clsAttrs <- iopdEmpty
    !clsEffs <- iopdEmpty
    !clsAnnos <- iopdEmpty
    !clsScopes <- newTVar []
    !clsRegions <- newTVar []
    !clsSyms <- newTVar TreeMap.empty
    let !pwip =
          EL'AnaProc
            clsExts
            clsExps
            clsAttrs
            clsEffs
            clsAnnos
            clsScopes
            clsRegions
            clsSyms
        !eacCls =
          EL'Context
            { el'ctx'scope =
                EL'ClassWIP
                  ( EL'DefineClass
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
        !cls'exps <- iopdSnapshot clsExps
        !scope'attrs <- iopdSnapshot clsAttrs
        !scope'effs <- iopdSnapshot clsEffs
        !innerScopes <- readTVar clsScopes
        !regions <- readTVar clsRegions
        !scope'symbols <- readTVar clsSyms
        let !cls'scope =
              EL'Scope
                { el'scope'span = body'span,
                  el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                  el'scope'regions = V.fromList $! reverse regions,
                  el'scope'attrs = scope'attrs,
                  el'scope'effs = scope'effs,
                  el'scope'symbols =
                    V.fromList $ snd <$> TreeMap.toAscList scope'symbols
                }
        -- record as an inner scope of outer scope
        modifyTVar' (el'scope'inner'scopes'wip outerProc) (cls'scope :)

        el'ResolveAttrAddr eas cls'name >>= \case
          Nothing -> el'Exit eas exit $ EL'Const nil
          Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
          Just !clsName -> do
            !clsAnno <- newTVar =<< el'ResolveAnnotation outerScope clsName
            let !mro = [] -- TODO C3 linearize cls'exts to get this
                !cls = EL'Class clsName cls'exts mro cls'scope cls'exps
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
              if el'ctx'eff'defining eac
                then iopdInsert clsName clsDef $ el'scope'effs'wip outerProc
                else do
                  let !attrs = el'scope'attrs'wip outerProc
                  iopdInsert clsName clsDef attrs
                  -- record as definition symbol of outer scope
                  recordScopeSymbol outerProc $ EL'DefSym clsDef
                  -- record a region after this definition for current scope
                  iopdSnapshot attrs
                    >>= modifyTVar' (el'scope'regions'wip pwip) . (:)
                      . EL'Region (src'end expr'span)

              when (el'ctx'exporting eac) $
                iopdInsert clsName clsDef $ el'scope'exps'wip outerProc

            -- return the class object value
            el'Exit eas exit clsVal
    where
      !eac = el'context eas
      !outerScope = el'ctx'scope eac
      !outerProc = el'ProcWIP outerScope
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
               !argsPkr
             )
           !expr'span
         )
  !exit
  !eas = do
    !nsExts <- newTVar []
    !nsExps <- iopdEmpty
    !nsAttrs <- iopdEmpty
    !nsEffs <- iopdEmpty
    !nsAnnos <- iopdEmpty
    !nsScopes <- newTVar []
    !nsRegions <- newTVar []
    !nsSyms <- newTVar TreeMap.empty
    let !pwip =
          EL'AnaProc
            nsExts
            nsExps
            nsAttrs
            nsEffs
            nsAnnos
            nsScopes
            nsRegions
            nsSyms
        !eacNs =
          EL'Context
            { el'ctx'scope = EL'ObjectWIP (EL'InitObject nsExts nsExps) pwip,
              el'ctx'outers = outerScope : el'ctx'outers eac,
              el'ctx'pure = False,
              el'ctx'exporting = False,
              el'ctx'eff'defining = False,
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
      el'RunTx easNs $
        el'AnalyzeStmts [ns'body] $ \_ _eas ->
          do
            -- update annotations for arguments from body
            forM_ argArts $ \(!argName, !argDef) ->
              iopdLookup argName nsAnnos >>= \case
                Nothing -> pure ()
                Just !anno ->
                  writeTVar (el'attr'def'anno argDef) $ Just anno
            --

            !ns'exts <- readTVar nsExts
            !ns'exps <- iopdSnapshot nsExps
            !scope'attrs <- iopdSnapshot nsAttrs
            !scope'effs <- iopdSnapshot nsEffs
            !innerScopes <- readTVar nsScopes
            !regions <- readTVar nsRegions
            !scope'symbols <- readTVar nsSyms
            let !ns'scope =
                  EL'Scope
                    { el'scope'span = body'span,
                      el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                      el'scope'regions = V.fromList $! reverse regions,
                      el'scope'attrs = scope'attrs,
                      el'scope'effs = scope'effs,
                      el'scope'symbols =
                        V.fromList $ snd <$> TreeMap.toAscList scope'symbols
                    }
            -- record as an inner scope of outer scope
            modifyTVar' (el'scope'inner'scopes'wip outerProc) (ns'scope :)

            el'ResolveAttrAddr eas ns'name >>= \case
              Nothing -> el'Exit eas exit $ EL'Const nil
              Just (AttrByName "_") -> el'Exit eas exit $ EL'Const nil
              Just !nsName -> do
                !nsAnno <- newTVar =<< el'ResolveAnnotation outerScope nsName
                let !ns =
                      EL'Object
                        el'NamespaceClass
                        ns'exts
                        scope'attrs
                        ns'exps
                    !nsVal = EL'ObjVal ns
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
                --

                -- record as artifact of outer scope
                unless (el'ctx'pure eac) $ do
                  if el'ctx'eff'defining eac
                    then iopdInsert nsName nsDef $ el'scope'effs'wip outerProc
                    else do
                      let !attrs = el'scope'attrs'wip outerProc
                      iopdInsert nsName nsDef attrs
                      -- record as definition symbol of outer scope
                      recordScopeSymbol outerProc $ EL'DefSym nsDef
                      -- record a region after this definition for current scope
                      iopdSnapshot attrs
                        >>= modifyTVar' (el'scope'regions'wip outerProc) . (:)
                          . EL'Region (src'end expr'span)

                  when (el'ctx'exporting eac) $
                    iopdInsert nsName nsDef $ el'scope'exps'wip outerProc

                -- return the namespace object value
                el'Exit eas exit nsVal
    where
      !eac = el'context eas
      !outerScope = el'ctx'scope eac
      !outerProc = el'ProcWIP outerScope
      diags = el'ctx'diags eac
--

-- scoped block
el'AnalyzeExpr _docCmt (ExprSrc (ScopedBlockExpr !stmts) !blk'span) !exit !eas =
  do
    !blkAttrs <- iopdEmpty
    !blkEffs <- iopdEmpty
    !blkAnnos <- iopdEmpty
    !blkScopes <- newTVar []
    !blkRegions <- newTVar []
    !blkSyms <- newTVar TreeMap.empty
    let !pwip =
          outerProc -- inherit exts/exps from outer scope
            { el'scope'attrs'wip = blkAttrs,
              el'scope'effs'wip = blkEffs,
              el'scope'annos'wip = blkAnnos,
              el'scope'inner'scopes'wip = blkScopes,
              el'scope'regions'wip = blkRegions,
              el'scope'symbols'wip = blkSyms
            }
        !eacBlk =
          eac
            { el'ctx'scope = EL'ProcWIP pwip,
              el'ctx'outers = outerScope : el'ctx'outers eac
            }
        !easBlk = eas {el'context = eacBlk}

    el'RunTx easBlk $
      el'AnalyzeStmts stmts $ \ !resultVal _eas -> do
        !scope'attrs <- iopdSnapshot blkAttrs
        !scope'effs <- iopdSnapshot blkEffs
        !innerScopes <- readTVar blkScopes
        !regions <- readTVar blkRegions
        !scope'symbols <- readTVar blkSyms
        let !blk'scope =
              EL'Scope
                { el'scope'span = blk'span,
                  el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                  el'scope'regions = V.fromList $! reverse regions,
                  el'scope'attrs = scope'attrs,
                  el'scope'effs = scope'effs,
                  el'scope'symbols =
                    V.fromList $ snd <$> TreeMap.toAscList scope'symbols
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
el'AnalyzeExpr _docCmt x@(ExprSrc (CaseExpr !tgt !bs) _expr'span) !exit !eas =
  el'RunTx eas $
    el'AnalyzeExpr Nothing tgt $
      const $ el'AnalyzeExpr Nothing bs $ const $ el'ExitTx exit $ EL'Expr x
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
      iopdUpdate loopArts attrs
      -- record a region before the loop body for current scope
      iopdSnapshot attrs
        >>= modifyTVar' (el'scope'regions'wip pwip) . (:)
          . EL'Region (src'start body'span)

    el'RunTx eas $
      el'AnalyzeExpr Nothing it $
        const $ el'AnalyzeStmt body $ const $ el'ExitTx exit $ EL'Expr x
    where
      !eac = el'context eas
      !swip = el'ctx'scope eac
      !pwip = el'ProcWIP swip
      !attrs = el'scope'attrs'wip pwip
      !annos = el'scope'annos'wip pwip

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
    let !symVal = EL'Const $ EdhSymbol sym

    -- record as artifact of current scope
    unless (el'ctx'pure eac) $ do
      !symAnno <- newTVar Nothing
      let !attrs = el'scope'attrs'wip pwip
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
      iopdInsert symName symDef attrs
      -- record as definition symbol of current scope
      recordScopeSymbol pwip $ EL'DefSym symDef
      -- record a region after this definition for current scope
      iopdSnapshot attrs
        >>= modifyTVar' (el'scope'regions'wip pwip) . (:)
          . EL'Region (src'end expr'span)

      when (el'ctx'exporting eac) $
        iopdInsert symName symDef $ el'scope'exps'wip pwip

    -- return the symbol value
    el'Exit eas exit symVal
  where
    !eac = el'context eas
    !swip = el'ctx'scope eac
    !pwip = el'ProcWIP swip

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
    !mthScopes <- newTVar []
    !mthRegions <- newTVar []
    !mthSyms <- newTVar TreeMap.empty
    let !pwip =
          outerProc -- inherit exts/exps from outer scope
            { el'scope'attrs'wip = mthAttrs,
              el'scope'effs'wip = mthEffs,
              el'scope'annos'wip = mthAnnos,
              el'scope'inner'scopes'wip = mthScopes,
              el'scope'regions'wip = mthRegions,
              el'scope'symbols'wip = mthSyms
            }
        !eacMth =
          EL'Context
            { el'ctx'scope = EL'ProcWIP pwip,
              el'ctx'outers = outerScope : el'ctx'outers eac,
              el'ctx'pure = False,
              el'ctx'exporting = False,
              el'ctx'eff'defining = False,
              el'ctx'diags = el'ctx'diags eac
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
        !innerScopes <- readTVar mthScopes
        !regions <- readTVar mthRegions
        !scope'symbols <- readTVar mthSyms
        let !mth'scope =
              EL'Scope
                { el'scope'span = body'span,
                  el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                  el'scope'regions = V.fromList $! reverse regions,
                  el'scope'attrs = scope'attrs,
                  el'scope'effs = scope'effs,
                  el'scope'symbols =
                    V.fromList $ snd <$> TreeMap.toAscList scope'symbols
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
            --

            -- record as artifact of outer scope
            unless (el'ctx'pure eac) $ do
              if el'ctx'eff'defining eac
                then iopdInsert mthName mthDef $ el'scope'effs'wip outerProc
                else do
                  let !attrs = el'scope'attrs'wip outerProc
                  iopdInsert mthName mthDef attrs
                  -- record as definition symbol of outer scope
                  recordScopeSymbol outerProc $ EL'DefSym mthDef
                  -- record a region after this definition for current scope
                  iopdSnapshot attrs
                    >>= modifyTVar' (el'scope'regions'wip pwip) . (:)
                      . EL'Region (src'end body'span)

              when (el'ctx'exporting eac) $
                iopdInsert mthName mthDef $ el'scope'exps'wip outerProc

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
        !mthSyms <- newTVar TreeMap.empty
        let !pwip =
              outerProc -- inherit exts/exps from outer scope
                { el'scope'attrs'wip = mthAttrs,
                  el'scope'effs'wip = mthEffs,
                  el'scope'annos'wip = mthAnnos,
                  el'scope'inner'scopes'wip = mthScopes,
                  el'scope'regions'wip = mthRegions,
                  el'scope'symbols'wip = mthSyms
                }
            !eacMth =
              EL'Context
                { el'ctx'scope = EL'ProcWIP pwip,
                  el'ctx'outers = outerScope : el'ctx'outers eac,
                  el'ctx'pure = False,
                  el'ctx'exporting = False,
                  el'ctx'eff'defining = False,
                  el'ctx'diags = el'ctx'diags eac
                }
            !easMth = eas {el'context = eacMth}

        !argArts <- case argsRcvr of
          WildReceiver -> return []
          PackReceiver !ars -> defArgArts ars
          SingleReceiver !ar -> defArgArts [ar]
        iopdUpdate argArts mthAttrs

        el'RunTx easMth $
          el'AnalyzeExpr Nothing rhExpr $ \_ _eas -> do
            -- update annotations for arguments from body
            forM_ argArts $ \(!argName, !argDef) ->
              iopdLookup argName mthAnnos >>= \case
                Nothing -> pure ()
                Just !anno -> writeTVar (el'attr'def'anno argDef) $ Just anno
            --
            !scope'attrs <- iopdSnapshot mthAttrs
            !scope'effs <- iopdSnapshot mthEffs
            !innerScopes <- readTVar mthScopes
            !regions <- readTVar mthRegions
            !scope'symbols <- readTVar mthSyms
            let !mth'scope =
                  EL'Scope
                    { el'scope'span = body'span,
                      el'scope'inner'scopes = V.fromList $! reverse innerScopes,
                      el'scope'regions = V.fromList $! reverse regions,
                      el'scope'attrs = scope'attrs,
                      el'scope'effs = scope'effs,
                      el'scope'symbols =
                        V.fromList $ snd <$> TreeMap.toAscList scope'symbols
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
