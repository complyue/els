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
                  modifyTVar' (el'modu'dependants resolved) $
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
                      <$> readTVar (el'modu'dependencies resolved') >>= \case
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
           in readTVar (el'modu'dependants resolved)
                >>= invalidateDependants [] . Map.toList

-- el'ResolveModule :: EL'Analysis EL'ResolvedModule
-- el'ResolveModule !exit !eas = el'RunTx eas $
--   el'ParseModule $ \ !pm _eas ->
--     let !mrVar = el'modu'resolution ms
--         goResolve :: STM ()
--         goResolve =
--           readTVar mrVar >>= \case
--             Just !rmVar -> el'Exit eas exit rmVar
--             Nothing -> do
--               !rmVar <- newEmptyTMVar
--               tryPutTMVar mrVar rmVar >>= \case
--                 False -> goResolve
--                 True -> do
--                   runEdhTx (el'ets eas) $
--                     forkEdh
--                       id
--                       ( edhCatchTx
--                           ( \ !exitTry !etsTry ->
--                               el'RunTx eas {el'ets = etsTry} $
--                                 el'DoResolveModule pm rmVar $ \() _eas ->
--                                   exitEdh etsTry exitTry nil
--                           )
--                           endOfEdh
--                           $ \ !recover !rethrow !etsCatching ->
--                             case edh'ctx'match $ edh'context etsCatching of
--                               EdhNil -> do
--                                 void $ -- in case it's not filled
--                                   tryPutTMVar rmVar $
--                                     EL'ResolvedModule
--                                       ( EL'Scope
--                                           noSrcRange
--                                           V.empty
--                                           odEmpty
--                                           odEmpty
--                                           V.empty
--                                       )
--                                       [ el'Diag
--                                           el'Error
--                                           noSrcRange
--                                           "no-resolve"
--                                           "module not resolved"
--                                       ]
--                                 runEdhTx etsCatching $ rethrow nil
--                               !exv -> edhValueDesc etsCatching exv $
--                                 \ !exDesc -> do
--                                   void $ -- in case it's not filled
--                                     tryPutTMVar rmVar $
--                                       EL'ResolvedModule
--                                         ( EL'Scope
--                                             noSrcRange
--                                             V.empty
--                                             odEmpty
--                                             odEmpty
--                                             V.empty
--                                         )
--                                         [ el'Diag
--                                             el'Error
--                                             noSrcRange
--                                             "err-resolve"
--                                             exDesc
--                                         ]
--                                   runEdhTx etsCatching $ recover nil
--                       )
--                       endOfEdh
--                   el'Exit eas exit rmVar
--      in goResolve
--   where
--     eac = el'context eas
--     ms = el'ctx'module eac

-- asModuleResolved :: EL'ModuSlot -> (EL'ResolvedModule -> STM ()) -> STM ()
-- asModuleResolved !ms !act =
--   readTVar (el'modu'resolution ms) >>= \case
--     EL'ModuResolving !acts -> modifyTVar' acts (act :)
--     EL'ModuResolved !resolvedModu -> act resolvedModu

asModuleParsed :: (EL'ParsedModule -> EL'Tx) -> EL'Tx
asModuleParsed !act' !eas =
  void $
    tryReadTMVar parsingVar >>= \case
      Nothing -> do
        !acts <- newTVar [\ !modu -> el'RunTx eas $ act' modu]
        tryPutTMVar parsingVar (EL'ModuParsing acts) >>= \case
          True -> doParseModule $ \ !parsed -> do
            -- installed the parsed record
            tryTakeTMVar parsingVar >>= \case
              Just (EL'ModuParsing acts')
                | acts' == acts ->
                  putTMVar parsingVar $ EL'ModuParsed parsed
              Just !other ->
                -- TODO this possible ?
                putTMVar parsingVar other
              _ -> error "bug: parsing record lost"
            -- trigger post actions
            readTVar acts >>= sequence_ . (<*> pure parsed)
          False -> retry -- avoid duplicate efforts
      Just (EL'ModuParsing !acts) -> modifyTVar' acts $
        (:) $ \ !parsed ->
          el'RunTx eas $ act' parsed
      Just (EL'ModuParsed !parsed) -> el'RunTx eas $ act' parsed
  where
    !eac = el'context eas
    !ms = el'ctx'module eac
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
            SrcDoc !moduFile = el'modu'doc $ el'ctx'module eac

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

-- el'DoResolveModule ::
--   EL'ParsedModule ->
--   EL'Analysis EL'ResolvedModule
-- el'DoResolveModule
--   (EL'ParsedModule _doc'cmt !stmts _parse'diags)
--   !exit
--   !eas = do
--     !diagsVar <- newTVar []
--     let !eac = (el'context eas) {el'ctx'diags = diagsVar}
--         !easModu = eas {el'context = eac}
--     el'RunTx easModu $
--       el'AnalyzeStmts stmts $ \_ _eas -> do
--         !diags <- readTVar diagsVar
--         let !swip = el'wip'proc $ el'ctx'scope eac
--         !scope'attrs <- iopdSnapshot $ el'scope'attrs'wip swip
--         !scope'effs <- iopdSnapshot $ el'scope'effs'wip swip
--         !scope'end <- readTVar $ el'scope'end'wip swip
--         !secs <- readTVar $ el'scope'secs'wip swip
--         !scope'symbols <- readTVar $ el'scope'symbols'wip swip
--         let !fullRegion =
--               EL'RegionSec $
--                 EL'Region
--                   { el'region'span = SrcRange beginningSrcPos scope'end,
--                     el'region'attrs = scope'attrs
--                   }
--         let !el'scope =
--               EL'Scope
--                 { el'scope'span = SrcRange beginningSrcPos scope'end,
--                   el'scope'sections = V.fromList $! reverse $ fullRegion : secs,
--                   el'scope'attrs = scope'attrs,
--                   el'scope'effs = scope'effs,
--                   el'scope'symbols = V.fromList $! reverse scope'symbols
--                 }
--             resolved :: EL'ResolvedModule
--             !resolved = EL'ResolvedModule el'scope $! reverse diags
--         el'Exit eas exit resolved

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
  ImportExpr !argsRcvr impSpec@(ExprSrc !specExpr !spec'span) !maybeInto ->
    case maybeInto of
      Just _intoExpr ->
        returnAsExpr -- TODO handle importing into some object
      Nothing -> case specExpr of
        LitExpr (StringLiteral !litSpec) -> el'RunTx eas $
          el'LocateImportee litSpec $ \ !impResult _eas -> case impResult of
            Left !err -> do
              el'LogDiag diags el'Error spec'span "err-import" err
              el'Exit eas exit $ EL'Const nil
        -- Right !msFrom -> el'RunTx
        --   eas
        --     { el'context = eac {el'ctx'module = msFrom}
        --     }
        --   $ el'ResolveModule $ \ !resolvedImporteeVar _eas ->
        --     readTMVar resolvedImporteeVar >>= \_resolvedImportee ->
        --       tryReadTMVar (el'modu'exports msFrom) >>= \case
        --         Just !expsFrom ->
        --           undefined -- TODO importee already resolved
        --         Nothing ->
        --           undefined -- TODO importee not resolved yet
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
  _ -> returnAsExpr
  where
    !eac = el'context eas
    diags = el'ctx'diags eac
    returnAsExpr = el'Exit eas exit $ EL'Expr xsrc
