module Language.Edh.Meta.World where

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import Data.Maybe
import Data.Text (Text)
import qualified Data.Vector as V
import Language.Edh.EHI
import Language.Edh.Meta.Analyze
import Language.Edh.Meta.Model
import Language.Edh.Meta.RtTypes
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
                [ ("locate", EdhMethod, wrapHostProc locateProc)
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
    elwAllocator !ctorExit _etsCtor = do
      !homes <- newTMVar V.empty
      !eow <- newEventSink
      let !elw = EL'World homes eow
      ctorExit $ HostStore (toDyn elw)

    homesProc :: EdhHostProc
    homesProc !exit !ets = withThisHostObj ets $ \ !elw ->
      readTMVar (el'homes elw) >>= \ !homes -> do
        let !hvs = V.toList $ V.map (EdhString . el'home'path) homes
        exitEdh ets exit $ EdhArgsPack $ ArgsPack hvs odEmpty

    locateProc :: "moduleFile" !: Text -> EdhHostProc
    locateProc (mandatoryArg -> !moduFile) !exit !ets =
      withThisHostObj ets $ \ !elw ->
        runEdhTx ets $
          el'LocateModule elw moduFile $ \ !ms _ets ->
            edhCreateHostObj msClass (toDyn ms) []
              >>= \ !msObj -> exitEdh ets exit $ EdhObject msObj
