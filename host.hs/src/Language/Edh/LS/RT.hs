module Language.Edh.LS.RT where

import           Prelude

import           System.Posix.IO
import           System.Posix.Types

import           Control.Concurrent.STM

import           Data.Text                      ( Text )
import qualified Data.Text                     as T


import           Language.Edh.EHI


sendTextToFd :: "fd" !: Int -> "txt" !: Text -> EdhHostProc
sendTextToFd (mandatoryArg -> !fd) (mandatoryArg -> !txt) !exit !ets =
  edhContIO writeIt ets
 where
  fd'     = Fd $ fromIntegral fd
  writeIt = do
    !bytesWritten <- fdWrite fd' (T.unpack txt)
    closeFd fd'
    atomically $ exitEdh ets exit $ EdhDecimal $ fromIntegral bytesWritten

