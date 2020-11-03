module Language.Edh.LS where

import           Prelude
-- import           Debug.Trace

import           Control.Exception
import           Control.Monad.Reader
import           Control.Concurrent
import           Control.Concurrent.STM

import qualified Data.Text                     as T

import           Language.Edh.EHI
import           Language.Edh.Net

import           Language.Edh.LS.RtTypes


installLanguageServerBatteries :: EdhWorld -> IO ()
installLanguageServerBatteries !world =
  void $ installEdhModule world "els/RT" $ \ !ets !exit ->

    -- loosely depend on the @net@ runtime from nedh package
    runEdhTx ets $ importEdhModule "net/RT" $ \case
      EdhObject !moduNetRT -> \_ets ->
        lookupEdhObjAttr moduNetRT (AttrByName "Peer") >>= \case
          (_, EdhObject !peerClass) -> do

            let !moduScope = contextScope $ edh'context ets

            !moduArts <-
              sequence
                $ [ (nm, ) <$> mkHostProc moduScope mc nm hp
                  | (nm, mc, hp) <- []
                  ]

            !artsDict <- EdhDict
              <$> createEdhDict [ (EdhString k, v) | (k, v) <- moduArts ]
            flip iopdUpdate (edh'scope'entity moduScope)
              $  [ (AttrByName k, v) | (k, v) <- moduArts ]
              ++ [(AttrByName "__exports__", artsDict)]

            exit
          _ -> error "bug: net/RT provides no Peer class"
      _ -> error "bug: importEdhModule returned non-object"


