module Language.Edh.Meta.World where

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import Data.Maybe
import Data.Text (Text)
import qualified Data.Vector as V
import Language.Edh.EHI
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
                [ ("invalidate", EdhMethod, wrapHostProc invalidateProc)
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

createMetaWorldClass :: Object -> Scope -> STM Object
createMetaWorldClass !msClass !clsOuterScope =
  mkHostClass clsOuterScope "MetaWorld" (allocEdhObj elwAllocator) [] $
    \ !clsScope -> do
      !arts <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsOuterScope vc nm hp
            | (nm, vc, hp) <-
                [ ("locate", EdhMethod, wrapHostProc locateProc),
                  ("locateByFile", EdhMethod, wrapHostProc locateByFileProc)
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
            \ !resolvedMeta _ets -> do
              reportLater msMeta 100 -- TODO need better way to delay this
              -- return the world
              let !metaRootScope = el'resolved'scope resolvedMeta
                  !ambient = el'scope'attrs metaRootScope
                  !elw = EL'World homes ambient
              ctorExit $ HostStore (toDyn elw)
      where
        world = edh'prog'world $ edh'thread'prog etsCtor
        console = edh'world'console world
        logger = consoleLogger console

        reportLater :: EL'ModuSlot -> Int -> STM ()
        reportLater !msRoot !n =
          if n > 0
            then runEdhTx etsCtor $ edhContSTM $ reportLater msRoot (n - 1)
            else do
              -- log all parsing/resolution diags as error
              el'WalkParsingDiags msRoot $ logDiagsAsErr "parsing"
              el'WalkResolutionDiags msRoot $ logDiagsAsErr "resolution"
          where
            logDiagsAsErr !cate !ms !diags = forM_ diags $ \ !diag ->
              logger
                40 -- error
                (Just $ "<els-world: " <> cate <> ">")
                (ArgsPack [EdhString $ el'PrettyDiag ms diag] odEmpty)

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
