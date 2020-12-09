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
import Prelude

installLanguageServerBatteries :: EdhWorld -> IO ()
installLanguageServerBatteries !world =
  void $
    installEdhModule world "els/RT" $ \ !ets !exit ->
      -- loosely depend on the @net@ runtime from nedh package
      runEdhTx ets $
        importEdhModule "net/RT" $ \case
          EdhObject !moduNetRT -> \_ets ->
            lookupEdhObjAttr moduNetRT (AttrByName "Addr") >>= \case
              (_, EdhObject !addrClass) -> do
                let !moduScope = contextScope $ edh'context ets

                !msClass <- createMetaModuleClass moduScope
                !mwClass <- createMetaWorldClass msClass moduScope
                !lsClass <- createLangServerClass addrClass moduScope

                !moduMths <-
                  sequence $
                    [ (AttrByName nm,) <$> mkHostProc moduScope mc nm hp
                      | (nm, mc, hp) <-
                          [("sendTextToFd", EdhMethod, wrapHostProc sendTextToFd)]
                    ]

                let !moduArts =
                      moduMths
                        ++ [ (AttrByName "MetaModule", EdhObject msClass),
                             (AttrByName "MetaWorld", EdhObject mwClass),
                             (AttrByName "LangServer", EdhObject lsClass)
                           ]
                !artsDict <-
                  EdhDict
                    <$> createEdhDict [(attrKeyValue k, v) | (k, v) <- moduArts]
                flip iopdUpdate (edh'scope'entity moduScope) $
                  [(k, v) | (k, v) <- moduArts]
                    ++ [(AttrByName "__exports__", artsDict)]

                exit
              _ -> error "bug: net/RT provides no Addr class"
          _ -> error "bug: importEdhModule returned non-object"
