module Language.Edh.LS
  ( installLanguageServerBatteries,
  -- TODO re-export other public artifacts
  )
where

-- import           Debug.Trace

import Control.Monad
import Language.Edh.LS.LangServer
import Language.Edh.LS.RT
import Language.Edh.MHI
import Language.Edh.Meta.World
import Language.Edh.Net
import Prelude

installLanguageServerBatteries :: EdhWorld -> IO ()
installLanguageServerBatteries !world =
  void $
    installModuleM world "els/RT" $ do
      !moduScope <- contextScope . edh'context <$> edhThreadState

      -- loosely depend on the @net@ runtime from nedh package
      !clsAddr <- getAddrClass

      !msClass <- createMetaModuleClass
      !mwClass <- createMetaWorldClass msClass
      !lsClass <- createLangServerClass clsAddr

      !moduMths <-
        sequence $
          [ (AttrByName nm,) <$> mkEdhProc mc nm hp
            | (nm, mc, hp) <-
                [ ( "sendTextToFd",
                    EdhMethod,
                    wrapEdhProc sendTextToFd
                  )
                ]
          ]

      let !moduArts =
            moduMths
              ++ [ (AttrByName "MetaModule", EdhObject msClass),
                   (AttrByName "MetaWorld", EdhObject mwClass),
                   (AttrByName "LangServer", EdhObject lsClass)
                 ]

      iopdUpdateEdh moduArts $ edh'scope'entity moduScope
      !esExps <- prepareExpStoreM (edh'scope'this moduScope)
      iopdUpdateEdh moduArts esExps
