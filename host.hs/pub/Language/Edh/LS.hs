module Language.Edh.LS where

import           Prelude
-- import           Debug.Trace

import           Control.Monad

import           Language.Edh.EHI

import           Language.Edh.LS.CC


installLanguageServerBatteries :: EdhWorld -> IO ()
installLanguageServerBatteries !world =
  void $ installEdhModule world "els/RT" $ \ !ets !exit ->

    -- loosely depend on the @net@ runtime from nedh package
    runEdhTx ets $ importEdhModule "net/RT" $ \case
      EdhObject !moduNetRT -> \_ets ->
        lookupEdhObjAttr moduNetRT (AttrByName "Addr") >>= \case
          (_, EdhObject !addrClass) -> do

            let !moduScope = contextScope $ edh'context ets

            !ccClass  <- createCCClass addrClass moduScope

            !moduMths <-
              sequence
                $ [ (AttrByName nm, ) <$> mkHostProc moduScope mc nm hp
                  | (nm, mc, hp) <- []
                  ]

            let !moduArts = (AttrByName "CC", EdhObject ccClass) : moduMths
            !artsDict <- EdhDict
              <$> createEdhDict [ (attrKeyValue k, v) | (k, v) <- moduArts ]
            flip iopdUpdate (edh'scope'entity moduScope)
              $  [ (k, v) | (k, v) <- moduArts ]
              ++ [(AttrByName "__exports__", artsDict)]

            exit

          _ -> error "bug: net/RT provides no Addr class"
      _ -> error "bug: importEdhModule returned non-object"


