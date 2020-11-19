module Language.Edh.LS where

-- import           Debug.Trace

import Control.Monad
import Language.Edh.EHI
import Language.Edh.LS.LangServer
import Language.Edh.LS.RT
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

                !lsClass <- createLangServerClass addrClass moduScope

                !moduMths <-
                  sequence $
                    [ (AttrByName nm,) <$> mkHostProc moduScope mc nm hp
                      | (nm, mc, hp) <-
                          [("sendTextToFd", EdhMethod, wrapHostProc sendTextToFd)]
                    ]

                let !moduArts =
                      (AttrByName "LangServer", EdhObject lsClass) : moduMths
                !artsDict <-
                  EdhDict
                    <$> createEdhDict [(attrKeyValue k, v) | (k, v) <- moduArts]
                flip iopdUpdate (edh'scope'entity moduScope) $
                  [(k, v) | (k, v) <- moduArts]
                    ++ [(AttrByName "__exports__", artsDict)]

                exit
              _ -> error "bug: net/RT provides no Addr class"
          _ -> error "bug: importEdhModule returned non-object"
