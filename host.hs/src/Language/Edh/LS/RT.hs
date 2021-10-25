module Language.Edh.LS.RT where

import Control.Monad.IO.Class
import Data.Text (Text)
import qualified Data.Text as T
import Language.Edh.MHI
import System.Posix.IO
import System.Posix.Types
import Prelude

sendTextToFd :: "fd" !: Int -> "txt" !: Text -> Edh EdhValue
sendTextToFd (mandatoryArg -> !fd) (mandatoryArg -> !txt) = liftIO writeIt
  where
    fd' = Fd $ fromIntegral fd
    writeIt = do
      !bytesWritten <- fdWrite fd' (T.unpack txt)
      closeFd fd'
      return $ EdhDecimal $ fromIntegral bytesWritten
