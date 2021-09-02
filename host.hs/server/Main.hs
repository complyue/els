module Main where

-- import           Debug.Trace

import Language.Edh.CHI
import Language.Edh.LS
import Language.Edh.Net
import Language.Edh.Run
import Prelude

main :: IO ()
main = edhRunModule defaultEdhConsoleSettings "els" $
  \ !world -> do
    -- install all necessary batteries
    installEdhBatteries world
    installNetBatteries world
    installLanguageServerBatteries world

    let !consoleOut = consoleIO (edh'world'console world) . ConsoleOut
    consoleOut ">> Đ (Edh) Language Server <<\n"
