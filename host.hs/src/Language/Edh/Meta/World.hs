module Language.Edh.Meta.World where

-- import Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import qualified Data.HashMap.Strict as Map
import Data.Maybe
import Data.Text (Text)
import qualified Data.Vector as V
import Language.Edh.EHI
import Language.Edh.LS.Json
import Language.Edh.Meta.Analyze
import Language.Edh.Meta.AtTypes
import Language.Edh.Meta.Model
import Prelude

createMetaModuleClass :: Scope -> STM Object
createMetaModuleClass !clsOuterScope =
  mkHostClass clsOuterScope "MetaModule" (allocEdhObj msAllocator) [] $
    \ !clsScope -> do
      !arts <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsOuterScope vc nm hp
            | (nm, vc, hp) <-
                [ ("invalidate", EdhMethod, wrapHostProc invalidateProc),
                  ("fill", EdhMethod, wrapHostProc fillProc)
                ]
          ]
            ++ [ (AttrByName nm,)
                   <$> mkHostProperty clsOuterScope nm getter setter
                 | (nm, getter, setter) <-
                     [ ("home", homeProc, Nothing),
                       ("doc", docProc, Nothing)
                     ]
               ]
      iopdUpdate arts $ edh'scope'entity clsScope
  where
    msAllocator :: EdhObjectAllocator
    msAllocator _ctorExit !etsCtor =
      throwEdh
        etsCtor
        EvalError
        "no way to construct MetaModule object from Edh code"

    homeProc :: EdhHostProc
    homeProc !exit !ets = withThisHostObj ets $ \ !ms -> do
      let !hv = EdhString $ el'home'path $ el'modu'home ms
      exitEdh ets exit hv

    docProc :: EdhHostProc
    docProc !exit !ets = withThisHostObj ets $ \ !ms -> do
      let SrcDoc !docFile = el'modu'doc ms
          !hv = EdhString docFile
      exitEdh ets exit hv

    invalidateProc :: "srcChanged" ?: Bool -> EdhHostProc
    invalidateProc (defaultArg False -> !srcChanged) !exit !ets =
      withThisHostObj ets $ \ !ms ->
        runEdhTx ets $
          el'InvalidateModule srcChanged ms $
            \() _ets -> exitEdh ets exit nil

    fillProc :: "srcOTF" !: Text -> EdhHostProc
    fillProc (mandatoryArg -> !srcOTF) !exit !ets =
      withThisHostObj ets $ \ !ms ->
        runEdhTx ets $
          el'FillModuleSource srcOTF ms $
            \_parsed _ets -> exitEdh ets exit nil

createMetaWorldClass :: Object -> Scope -> STM Object
createMetaWorldClass !msClass !clsOuterScope =
  mkHostClass clsOuterScope "MetaWorld" (allocEdhObj elwAllocator) [] $
    \ !clsScope -> do
      !arts <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsOuterScope vc nm hp
            | (nm, vc, hp) <-
                [ ("locate", EdhMethod, wrapHostProc locateProc),
                  ("locateByFile", EdhMethod, wrapHostProc locateByFileProc),
                  ("diags", EdhMethod, wrapHostProc diagsProc)
                ]
          ]
            ++ [ (AttrByName nm,)
                   <$> mkHostProperty clsOuterScope nm getter setter
                 | (nm, getter, setter) <-
                     [ ("homes", homesProc, Nothing)
                     ]
               ]
      iopdUpdate arts $ edh'scope'entity clsScope
  where
    elwAllocator :: EdhObjectAllocator
    elwAllocator !ctorExit !etsCtor = do
      !homes <- newTMVar V.empty
      let !bootstrapWorld = EL'World homes odEmpty
      runEdhTx etsCtor $
        el'LocateModule bootstrapWorld "batteries/meta" $
          \ !msMeta -> asModuleResolved bootstrapWorld msMeta $
            \ !resolvedMeta _ets ->
              let !piVar = el'pending'imps resolvedMeta
                  untilMetaFullyLoaded :: STM ()
                  untilMetaFullyLoaded =
                    {- HLINT ignore "Redundant <$>" -}
                    Map.null <$> readTVar piVar >>= \case
                      False ->
                        -- not fully loaded yet
                        runEdhTx etsCtor $ edhContSTM untilMetaFullyLoaded
                      True -> do
                        -- log all parsing/resolution diags as error
                        el'WalkParsingDiags msMeta $
                          logDiagsAsErr "Đ syntax"
                        el'WalkResolutionDiags msMeta $
                          logDiagsAsErr "Đ semantics"
                        -- return the world
                        let !metaRootScope = el'resolved'scope resolvedMeta
                            !ambient = el'scope'attrs metaRootScope
                            !elw = EL'World homes ambient
                        ctorExit $ HostStore (toDyn elw)
               in untilMetaFullyLoaded
      where
        world = edh'prog'world $ edh'thread'prog etsCtor
        console = edh'world'console world
        logger = consoleLogger console

        logDiagsAsErr !cate !ms !diags = forM_ diags $ \ !diag ->
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
                ( ArgsPack
                    [ EdhString $ cate <> ": " <> el'diag'message diag
                    ]
                    odEmpty
                )

    homesProc :: EdhHostProc
    homesProc !exit !ets = withThisHostObj ets $ \ !elw ->
      readTMVar (el'homes elw) >>= \ !homes -> do
        let !hvs = V.toList $ V.map (EdhString . el'home'path) homes
        exitEdh ets exit $ EdhArgsPack $ ArgsPack hvs odEmpty

    locateProc :: "moduSpec" !: Text -> EdhHostProc
    locateProc (mandatoryArg -> !moduSpec) !exit !ets =
      withThisHostObj ets $ \ !elw ->
        runEdhTx ets $
          el'LocateModule elw moduSpec $ \ !ms _ets ->
            edhCreateHostObj msClass (toDyn ms) []
              >>= \ !msObj -> exitEdh ets exit $ EdhObject msObj

    locateByFileProc :: "moduleFile" !: Text -> EdhHostProc
    locateByFileProc (mandatoryArg -> !moduFile) !exit !ets =
      withThisHostObj ets $ \ !elw ->
        runEdhTx ets $
          el'LocateModuleByFile elw moduFile $ \ !ms _ets ->
            edhCreateHostObj msClass (toDyn ms) []
              >>= \ !msObj -> exitEdh ets exit $ EdhObject msObj

    diagsProc :: "modu" !: EL'ModuSlot -> EdhHostProc
    diagsProc (mandatoryArg -> !ms) !exit !ets =
      withThisHostObj ets $ \ !elw ->
        runEdhTx ets $
          asModuleResolved elw ms $ \ !resolved _ets -> do
            !diags <-
              fmap (el'resolution'diags resolved ++) $
                tryReadTMVar (el'modu'parsing ms) >>= \case
                  Just (EL'ModuParsed !parsed) ->
                    return $ el'parsing'diags parsed
                  _ -> return []
            exitEdh ets exit $ jsonArray $ fmap toLSP diags
