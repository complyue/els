module Language.Edh.Meta.World where

import Control.Concurrent.STM
import Control.Monad
import Data.Maybe
import Data.Text (Text)
-- import qualified Data.Text as T
import qualified Data.Vector as V
-- import Debug.Trace

import Language.Edh.EHI
import Language.Edh.Evaluate
import Language.Edh.LS.Json
import Language.Edh.Meta.Analyze
import Language.Edh.Meta.AtTypes
import Language.Edh.Meta.Model
import Prelude

defineMetaModuleClass :: Edh Object
defineMetaModuleClass =
  defEdhClass' "MetaModule" msAllocator [] $ do
    defEdhProc'_ EdhMethod "moduSymbols" moduSymbolsProc
    defEdhProc'_ EdhMethod "foldingRanges" foldingRangesProc
    defEdhProc'_ EdhMethod "invalidate" invalidateProc
    defEdhProc'_ EdhMethod "fill" fillProc
    defEdhProc'_ EdhMethod "stabilized" stabilizedProc
    defEdhProperty_ "home" homeProc Nothing
    defEdhProperty_ "doc" docProc Nothing
  where
    msAllocator :: Edh ObjectStore
    msAllocator =
      throwEdhM
        EvalError
        "no way to construct MetaModule object from Edh code"

    withThisModuSlot :: forall r. (Object -> EL'ModuSlot -> Edh r) -> Edh r
    withThisModuSlot withMetaModu = do
      !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
      case unwrapHostValue =<< objHostValue this of
        Nothing -> throwEdhM EvalError "bug: this is not an MetaModu"
        Just !col -> withMetaModu this col

    moduSymbolsProc :: Edh EdhValue
    moduSymbolsProc = withThisModuSlot $ \_this !ms ->
      mEdh $ \ !exit !ets -> runEdhTx ets $
        asModuleParsed ms $
          \(EL'ParsedModule _ver !modu'cmt !stmts _diags) _ets ->
            exitEdh ets exit $
              jsonArray $
                toLSP <$> moduSymbols (el'modu'name ms) modu'cmt stmts

    foldingRangesProc :: Edh EdhValue
    foldingRangesProc = withThisModuSlot $ \_this !ms ->
      mEdh $ \ !exit !ets -> runEdhTx ets $
        asModuleParsed ms $
          \(EL'ParsedModule _ver _modu'cmt !stmts _diags) _ets ->
            exitEdh ets exit $
              jsonArray $
                toLSP
                  <$> blockFoldRngs stmts

    invalidateProc :: "srcChanged" ?: Bool -> Edh EdhValue
    invalidateProc (defaultArg False -> !srcChanged) =
      withThisModuSlot $ \_this !ms ->
        mEdh $ \ !exit !ets -> runEdhTx ets $
          el'InvalidateModule srcChanged ms $
            \() _ets -> exitEdh ets exit nil

    fillProc :: "verOTF" !: Int -> "srcOTF" !: Text -> Edh EdhValue
    fillProc (mandatoryArg -> !verOTF) (mandatoryArg -> !srcOTF) =
      withThisModuSlot $ \_this !ms ->
        mEdh $ \ !exit !ets ->
          runEdhTx ets $ el'FillModuleSource verOTF srcOTF ms $ exit . EdhBool

    stabilizedProc :: Edh EdhValue
    stabilizedProc = withThisModuSlot $ \_this !ms ->
      mEdh $ \ !exit !ets ->
        moduSrcStabilized ms >>= exitEdh ets exit . EdhBool

    homeProc :: Edh EdhValue
    homeProc = withThisModuSlot $ \_this !ms -> do
      let !hv = EdhString $ el'home'path $ el'modu'home ms
      return hv

    docProc :: Edh EdhValue
    docProc = withThisModuSlot $ \_this !ms -> do
      let SrcDoc !docFile = el'modu'doc ms
          !hv = EdhString docFile
      return hv

defineMetaWorldClass :: Object -> Edh Object
defineMetaWorldClass !msClass =
  defEdhClass' "MetaWorld" elwAllocator [] $ do
    defEdhProc'_ EdhMethod "locate" locateProc
    defEdhProc'_ EdhMethod "locateByFile" locateByFileProc
    defEdhProc'_ EdhMethod "diags" diagsProc
    defEdhProc'_ EdhMethod "defi" defiProc
    defEdhProc'_ EdhMethod "hover" hoverProc
    defEdhProc'_ EdhMethod "suggest" suggestProc
    defEdhProperty_ "homes" homesProc Nothing
  where
    elwAllocator :: Edh ObjectStore
    elwAllocator = do
      !homes <- newTMVarEdh V.empty
      let !bootstrapWorld = EL'World homes odEmpty
      mEdh $ \ !exit !ets -> do
        let world = edh'prog'world $ edh'thread'prog ets
            console = edh'world'console world
            logger = consoleLogger console
            logDiags !cate !ms !diags = forM_ diags $ \ !diag ->
              let !severity = case el'diag'severity diag of
                    -- TODO does PatternSynonyms worth its weight for here?
                    --      EL'DiagSeverity will need to be a newtype then
                    1 -> 40 -- error
                    2 -> 30 -- warning
                    3 -> 20 -- information
                    4 -> 10 -- hint -> debug
                    _ -> 30 -- others unknown
               in logger
                    severity
                    (Just $ el'PrettyLoc ms diag)
                    ( cate <> ": " <> el'diag'message diag
                    )

        runEdhTx ets $
          el'LocateModule bootstrapWorld "batteries/meta" $
            \ !msMeta -> asModuleResolved bootstrapWorld msMeta $
              \ !resolvedMeta _ets -> do
                when
                  ( consoleLogLevel
                      ( edh'world'console $
                          edh'prog'world $
                            edh'thread'prog ets
                      )
                      <= 10
                  )
                  $ do
                    -- log all parsing/resolution diags
                    el'WalkParsingDiags msMeta $ logDiags "Đ syntax"
                    el'WalkResolutionDiags msMeta $ logDiags "Đ semantics"
                -- make the meta scope for ambient of all modules
                let !metaRootScope = el'modu'scope resolvedMeta
                    !ambient = odMap metaDef (el'ScopeAttrs metaRootScope)
                    metaDef !def =
                      def
                        { el'attr'def'focus = noSrcRange,
                          el'attr'def'value = EL'External msMeta def,
                          el'attr'prev'def = Nothing
                        }
                    !elw = EL'World homes ambient

                -- return the world
                exitEdh ets exit . HostStore =<< pinHostValue elw

    withThisWorld :: forall r. (Object -> EL'World -> Edh r) -> Edh r
    withThisWorld withWorld = do
      !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
      case unwrapHostValue =<< objHostValue this of
        Nothing -> throwEdhM EvalError "bug: this is not an World"
        Just !col -> withWorld this col

    homesProc :: Edh EdhValue
    homesProc = withThisWorld $ \_this !elw -> inlineSTM $ do
      !homes <- readTMVar (el'homes elw)
      let !hvs = V.toList $ V.map (EdhString . el'home'path) homes
      return $ EdhArgsPack $ ArgsPack hvs odEmpty

    locateProc :: "moduSpec" !: Text -> Edh EdhValue
    locateProc (mandatoryArg -> !moduSpec) = withThisWorld $ \_this !elw ->
      mEdh $ \ !exit !ets -> runEdhTx ets $
        el'LocateModule elw moduSpec $ \ !ms _ets ->
          edhCreateHostObj msClass ms
            >>= \ !msObj -> exitEdh ets exit $ EdhObject msObj

    locateByFileProc :: "moduleFile" !: Text -> Edh EdhValue
    locateByFileProc (mandatoryArg -> !moduFile) =
      withThisWorld $ \_this !elw ->
        mEdh $ \ !exit !ets -> runEdhTx ets $
          el'LocateModuleByFile elw moduFile $ \ !ms _ets ->
            edhCreateHostObj msClass ms
              >>= \ !msObj -> exitEdh ets exit $ EdhObject msObj

    diagsProc :: "modu" !: EL'ModuSlot -> Edh EdhValue
    diagsProc (mandatoryArg -> !ms) = withThisWorld $ \_this !elw ->
      mEdh $ \ !exit !ets -> runEdhTx ets $
        asModuleResolved elw ms $ \ !resolved _ets -> do
          !diags <-
            fmap (el'resolution'diags resolved ++) $
              tryReadTMVar (el'modu'parsing ms) >>= \case
                Just (EL'ModuParsed !parsed) ->
                  return $ el'parsing'diags parsed
                _ -> return []
          exitEdh ets exit $ jsonArray $ fmap toLSP diags

    defiProc ::
      "modu" !: EL'ModuSlot ->
      "line" !: Int ->
      "char" !: Int ->
      Edh EdhValue
    defiProc
      (mandatoryArg -> !ms)
      (mandatoryArg -> !line)
      (mandatoryArg -> !char) = withThisWorld $ \_this !elw ->
        mEdh $ \ !exit !ets -> runEdhTx ets $
          asModuleResolved elw ms $ \ !resolved _ets ->
            case locateAttrRefInModule line char resolved of
              Nothing -> exitEdh ets exit $ jsonArray []
              Just !ref -> exitEdh ets exit $ toLSP ref

    hoverProc ::
      "modu" !: EL'ModuSlot ->
      "line" !: Int ->
      "char" !: Int ->
      Edh EdhValue
    hoverProc
      (mandatoryArg -> !ms)
      (mandatoryArg -> !line)
      (mandatoryArg -> !char) = withThisWorld $ \_this !elw ->
        mEdh $ \ !exit !ets -> runEdhTx ets $
          asModuleResolved elw ms $ \ !resolved _ets ->
            case el'AttrRefDoc <$> locateAttrRefInModule line char resolved of
              Nothing -> exitEdh ets exit jsonNull
              Just !doc -> exitEdh ets exit $ toLSP doc

    suggestProc ::
      "modu" !: EL'ModuSlot ->
      "line" !: Int ->
      "char" !: Int ->
      Edh EdhValue
    suggestProc
      (mandatoryArg -> !ms)
      (mandatoryArg -> !line)
      (mandatoryArg -> !char) = withThisWorld $ \_this !elw -> do
        inlineSTM $
          readTVar otfVar >>= \case
            Nothing -> pure ()
            Just (!ver, !src, _otfTime) ->
              -- mark as stablized
              writeTVar otfVar $ Just (ver, src, 0)
        mEdh $ \ !exit !ets -> runEdhTx ets $
          asModuleResolved elw ms $ \ !resolved _ets ->
            exitEdh ets exit . toLSP
              =<< suggestCompletions elw line char resolved
        where
          !otfVar = el'modu'src'otf ms
