module Language.Edh.LS
  ( installLanguageServerBatteries,
  -- TODO re-export other public artifacts
  )
where

-- import           Debug.Trace

import Control.Monad
import Language.Edh.EHI
import Language.Edh.LS.LangServer
import Language.Edh.LS.RT
import Language.Edh.Meta.World
import Language.Edh.Net
import Prelude

installLanguageServerBatteries :: EdhWorld -> IO ()
installLanguageServerBatteries !world =
  void $
    installEdhModule world "els/RT" $ \ !ets !exit -> runEdhTx ets $
      -- loosely depend on the @net@ runtime from nedh package
      withAddrClass $ \ !clsAddr _ets -> do
        let !moduScope = contextScope $ edh'context ets

        !msClass <- createMetaModuleClass moduScope
        !mwClass <- createMetaWorldClass msClass moduScope
        !lsClass <- createLangServerClass clsAddr moduScope

        !moduMths <-
          sequence $
            [ (AttrByName nm,) <$> mkHostProc moduScope mc nm hp
              | (nm, mc, hp) <-
                  [ ( "sendTextToFd",
                      EdhMethod,
                      wrapHostProc sendTextToFd
                    )
                  ]
            ]

        let !moduArts =
              moduMths
                ++ [ (AttrByName "MetaModule", EdhObject msClass),
                     (AttrByName "MetaWorld", EdhObject mwClass),
                     (AttrByName "LangServer", EdhObject lsClass)
                   ]
        iopdUpdate moduArts $ edh'scope'entity moduScope
        prepareExpStore ets (edh'scope'this moduScope) $ \ !esExps ->
          iopdUpdate moduArts esExps

        exit
