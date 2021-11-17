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
installLanguageServerBatteries !world = runProgramM_ world $ do
  installModuleM_ "els/RT" $ do
    -- loosely depend on the @net@ runtime from nedh package
    !clsAddr <- getAddrClass

    exportM_ $ do
      !msClass <- defineMetaModuleClass
      void $ defineMetaWorldClass msClass
      void $ defineLangServerClass clsAddr
      defEdhProc'_ EdhMethod "sendTextToFd" sendTextToFd
