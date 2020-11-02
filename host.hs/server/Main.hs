
module Main where

import           Prelude
-- import           Debug.Trace

import           Control.Monad
import           Control.Exception
import           Control.Concurrent
import           Control.Concurrent.STM

import qualified Data.Text                     as T

import           Language.Edh.EHI
import           Language.Edh.Net

import           Language.Edh.LS


main :: IO ()
main = do
  !console <- defaultEdhConsole defaultEdhConsoleSettings
  let !consoleOut = writeTBQueue (consoleIO console) . ConsoleOut
      runIt       = do

        world <- createEdhWorld console
        installEdhBatteries world

        -- install batteries provided by nedh
        installNetBatteries world

        -- install batteries provided by els
        installLanguageServerBatteries world

        runEdhModule world "els" edhModuleAsIs >>= \case
          Left !err -> atomically $ do
            -- program crash on error
            consoleOut "Đ (Edh) language server crashed with an error:\n"
            consoleOut $ T.pack $ show err <> "\n"
          Right !phv -> case edhUltimate phv of
            -- clean program halt, all done
            EdhNil -> return ()
            -- unclean program exit
            _      -> atomically $ do
              consoleOut "Đ (Edh) language server halted with a result:\n"
              consoleOut $ (<> "\n") $ case phv of
                EdhString msg -> msg
                _             -> T.pack $ show phv

  void $ forkFinally runIt $ \ !result -> do
    case result of
      Left (e :: SomeException) ->
        atomically $ consoleOut $ "💥 " <> T.pack (show e)
      Right _ -> pure ()
    -- shutdown console IO anyway
    atomically $ writeTBQueue (consoleIO console) ConsoleShutdown

  atomically $ consoleOut ">> Đ (Edh) Language Server <<\n"

  consoleIOLoop console
