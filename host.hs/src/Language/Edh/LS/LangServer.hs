module Language.Edh.LS.LangServer where

-- import           Debug.Trace

import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import Data.Dynamic
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding
import Language.Edh.EHI
import Language.Edh.LS.BaseLSP
import Language.Edh.Net
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)
import Prelude

data LangServer = LangServer
  { -- the import spec of the service module
    edh'lang'server'modu :: !Text,
    -- local network port to bind
    edh'lang'server'port :: !PortNumber,
    -- max port number to try bind
    edh'lang'server'port'max :: !PortNumber,
    -- local network interface to bind
    edh'lang'server'addr :: !Text,
    -- actually listened network addresses
    edh'lang'serving'addrs :: !(TMVar [AddrInfo]),
    -- end-of-life status
    edh'lang'server'eol :: !(TMVar (Either SomeException ())),
    -- service module initializer, must callable if not nil
    edh'lang'server'init :: !EdhValue
  }

createLangServerClass :: Object -> Scope -> STM Object
createLangServerClass !addrClass !clsOuterScope =
  mkHostClass clsOuterScope "LangServer" (allocEdhObj serverAllocator) [] $
    \ !clsScope -> do
      !mths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ("addrs", EdhMethod, wrapHostProc addrsProc),
                  ("eol", EdhMethod, wrapHostProc eolProc),
                  ("join", EdhMethod, wrapHostProc joinProc),
                  ("stop", EdhMethod, wrapHostProc stopProc),
                  ("__repr__", EdhMethod, wrapHostProc reprProc)
                ]
          ]
      iopdUpdate mths $ edh'scope'entity clsScope
  where
    serverAllocator ::
      "port" ?: Int ->
      "port'max" ?: Int ->
      "addr" ?: Text ->
      "modu" ?: Text ->
      "init" ?: EdhValue ->
      EdhObjectAllocator
    serverAllocator
      (defaultArg 1707 -> !ctorPort)
      (defaultArg ctorPort -> port'max)
      (defaultArg "127.0.0.1" -> !ctorAddr)
      (defaultArg "els/serve" -> !modu)
      (defaultArg nil -> !init_)
      !ctorExit
      !etsCtor =
        if edh'in'tx etsCtor
          then
            throwEdh
              etsCtor
              UsageError
              "you don't create network objects within a transaction"
          else case edhUltimate init_ of
            EdhNil -> withInit nil
            mth@(EdhProcedure EdhMethod {} _) -> withInit mth
            mth@(EdhBoundProc EdhMethod {} _ _ _) -> withInit mth
            !badInit -> edhValueDesc etsCtor badInit $ \ !badDesc ->
              throwEdh etsCtor UsageError $ "invalid init: " <> badDesc
        where
          withInit !__modu_init__ = do
            !servAddrs <- newEmptyTMVar
            !servEoL <- newEmptyTMVar
            let !server =
                  LangServer
                    { edh'lang'server'modu = modu,
                      edh'lang'server'port = fromIntegral ctorPort,
                      edh'lang'server'port'max = fromIntegral port'max,
                      edh'lang'server'addr = ctorAddr,
                      edh'lang'serving'addrs = servAddrs,
                      edh'lang'server'eol = servEoL,
                      edh'lang'server'init = __modu_init__
                    }
            runEdhTx etsCtor $
              edhContIO $ do
                void $
                  forkFinally
                    (serverThread server)
                    ( atomically
                        . void
                        -- fill empty addrs if the connection has ever failed
                        . (tryPutTMVar servAddrs [] <*)
                        -- mark server end-of-life anyway finally
                        . void
                        . tryPutTMVar servEoL
                    )
                atomically $ ctorExit Nothing $ HostStore (toDyn server)

          serverThread :: LangServer -> IO ()
          serverThread
            ( LangServer
                !servModu
                !servPort
                !portMax
                !servAddr
                !servAddrs
                !servEoL
                !__modu_init__
              ) =
              do
                servThId <- myThreadId
                void $
                  forkIO $ do
                    -- async terminate the accepter thread on stop signal
                    _ <- atomically $ readTMVar servEoL
                    killThread servThId
                addr <- resolveServAddr
                bracket (open addr) close acceptClients
              where
                world = edh'prog'world $ edh'thread'prog etsCtor

                resolveServAddr = do
                  let hints =
                        defaultHints
                          { addrFlags = [AI_PASSIVE],
                            addrSocketType = Stream
                          }
                  addr : _ <-
                    getAddrInfo
                      (Just hints)
                      (Just $ T.unpack servAddr)
                      (Just (show servPort))
                  return addr

                tryBind !ssock !addr !port =
                  catch (bind ssock $ addrWithPort addr port) $
                    \(e :: SomeException) ->
                      if port < portMax
                        then tryBind ssock addr (port + 1)
                        else throw e
                open addr =
                  bracketOnError
                    ( socket
                        (addrFamily addr)
                        (addrSocketType addr)
                        (addrProtocol addr)
                    )
                    close
                    $ \ssock -> do
                      tryBind ssock (addrAddress addr) servPort
                      listen ssock 3 -- todo make this tunable ?
                      listenAddr <- getSocketName ssock
                      {- HLINT ignore "Redundant <$>" -}
                      atomically $
                        fromMaybe []
                          <$> tryTakeTMVar servAddrs
                          >>= putTMVar servAddrs
                            . (addr {addrAddress = listenAddr} :)
                      return ssock

                acceptClients :: Socket -> IO ()
                acceptClients ssock = do
                  bracketOnError (accept ssock) (close . fst) $
                    \(sock, addr) -> do
                      clientEoL <- newEmptyTMVarIO
                      void $
                        forkFinally
                          (servClient clientEoL (T.pack $ show addr) sock)
                          $ (gracefulClose sock 5000 <*)
                            . atomically
                            . tryPutTMVar clientEoL
                  acceptClients ssock -- tail recursion
                servClient ::
                  TMVar (Either SomeException ()) ->
                  Text ->
                  Socket ->
                  IO ()
                servClient !clientEoL !clientId !sock = do
                  pktSink <- newEmptyTMVarIO
                  poq <- newEmptyTMVarIO

                  let ccEoLProc :: EdhHostProc
                      ccEoLProc !exit !ets =
                        tryReadTMVar clientEoL >>= \case
                          Nothing -> exitEdh ets exit $ EdhBool False
                          Just (Left !e) ->
                            edh'exception'wrapper world e
                              >>= \ !exo -> exitEdh ets exit $ EdhObject exo
                          Just (Right ()) -> exitEdh ets exit $ EdhBool True

                      recvOnePktProc :: Scope -> EdhHostProc
                      recvOnePktProc !sandbox !exit !ets =
                        (Right <$> takeTMVar pktSink)
                          `orElse` (Left <$> readTMVar clientEoL)
                          >>= \case
                            -- reached normal end-of-stream
                            Left Right {} -> exitEdh ets exit nil
                            -- previously eol due to error
                            Left (Left !ex) ->
                              edh'exception'wrapper
                                (edh'prog'world $ edh'thread'prog ets)
                                ex
                                >>= \ !exo -> edhThrow ets $ EdhObject exo
                            Right (Rpc _headers !content) -> do
                              -- interpret the content as command, return as is
                              let !src = decodeUtf8 content
                              runEdhInSandbox
                                ets
                                sandbox
                                (evalEdh ("lsc:" <> clientId) src)
                                $ \ !r _ets -> exitEdh ets exit r

                      postOnePktProc ::
                        "rpcOut" !: Text ->
                        RestKwArgs ->
                        EdhHostProc
                      postOnePktProc
                        (mandatoryArg -> !content)
                        !headers
                        !exit
                        !ets =
                          go
                            (odToList headers)
                            []
                          where
                            go ::
                              [(AttrKey, EdhValue)] ->
                              [(HeaderName, HeaderContent)] ->
                              STM ()
                            go [] !hdrs = do
                              void $ tryPutTMVar poq $ textRpc hdrs content
                              exitEdh ets exit nil
                            go ((k, v) : rest) !hdrs =
                              edhValueStr ets v $ \ !sv ->
                                go rest ((attrKeyStr k, sv) : hdrs)

                      prepService :: EdhModulePreparation
                      prepService !etsModu !exit =
                        mkObjSandbox etsModu moduObj $ \ !sandboxScope -> do
                          -- define and implant procedures to the module being
                          -- prepared
                          !moduMths <-
                            sequence
                              [ (AttrByName nm,)
                                  <$> mkHostProc moduScope vc nm hp
                                | (nm, vc, hp) <-
                                    [ ( "eol",
                                        EdhMethod,
                                        wrapHostProc
                                          ccEoLProc
                                      ),
                                      ( "recvOnePkt",
                                        EdhMethod,
                                        wrapHostProc $
                                          recvOnePktProc sandboxScope
                                      ),
                                      ( "postOnePkt",
                                        EdhMethod,
                                        wrapHostProc postOnePktProc
                                      )
                                    ]
                              ]
                          let !moduArts =
                                (AttrByName "clientId", EdhString clientId) :
                                moduMths
                          iopdUpdate moduArts $ edh'scope'entity moduScope

                          -- call the service module initialization method in
                          -- the module context (where both contextual this/that
                          -- are the module object)
                          if __modu_init__ == nil
                            then exit
                            else edhPrepareCall'
                              etsModu
                              __modu_init__
                              ( ArgsPack
                                  [EdhObject $ edh'scope'this moduScope]
                                  odEmpty
                              )
                              $ \ !mkCall -> runEdhTx etsModu $
                                mkCall $ \_result _ets -> exit
                        where
                          !moduScope = contextScope $ edh'context etsModu
                          !moduObj = edh'scope'this moduScope

                  -- run the server module on a separate thread as another
                  -- program
                  void $
                    forkFinally
                      (runEdhModule' world (T.unpack servModu) prepService)
                      -- mark client end-of-life with the result anyway
                      $ void
                        . atomically
                        . tryPutTMVar clientEoL
                        . void

                  -- pump commands in,
                  -- make this thread the only one reading the handle
                  -- note
                  --   this won't return, will be asynchronously killed on eol
                  void $
                    forkFinally
                      (receiveRpcStream clientId (recv sock) pktSink clientEoL)
                      -- mark client end-of-life upon disconnected or err out
                      $ void
                        . atomically
                        . tryPutTMVar clientEoL
                        . void

                  let serializeCmdsOut :: IO ()
                      serializeCmdsOut =
                        atomically
                          ( (Right <$> takeTMVar poq)
                              `orElse` (Left <$> readTMVar clientEoL)
                          )
                          >>= \case
                            Left _ -> return () -- stop on eol any way
                            Right !pkt -> do
                              sendRpc (sendAll sock) pkt
                              serializeCmdsOut
                  -- pump commands out,
                  -- make this thread the only one writing the handle
                  serializeCmdsOut `catch` \(e :: SomeException) ->
                    -- mark eol on error
                    atomically $ void $ tryPutTMVar clientEoL $ Left e

    reprProc :: EdhHostProc
    reprProc !exit !ets =
      withThisHostObj ets $ \(LangServer !modu !port !port'max !addr _ _ _) ->
        exitEdh ets exit $
          EdhString $
            "LangServer("
              <> T.pack (show port)
              <> ", "
              <> T.pack (show port'max)
              <> ", "
              <> T.pack (show addr)
              <> ", "
              <> T.pack (show modu)
              <> ")"

    addrsProc :: EdhHostProc
    addrsProc !exit !ets = withThisHostObj ets $
      \ !server -> readTMVar (edh'lang'serving'addrs server) >>= wrapAddrs []
      where
        wrapAddrs :: [EdhValue] -> [AddrInfo] -> STM ()
        wrapAddrs addrs [] =
          exitEdh ets exit $ EdhArgsPack $ ArgsPack addrs odEmpty
        wrapAddrs !addrs (addr : rest) =
          edhCreateHostObj addrClass addr
            >>= \ !addrObj -> wrapAddrs (EdhObject addrObj : addrs) rest

    eolProc :: EdhHostProc
    eolProc !exit !ets = withThisHostObj ets $ \ !server ->
      tryReadTMVar (edh'lang'server'eol server) >>= \case
        Nothing -> exitEdh ets exit $ EdhBool False
        Just (Left !e) ->
          edh'exception'wrapper world e
            >>= \ !exo -> exitEdh ets exit $ EdhObject exo
        Just (Right ()) -> exitEdh ets exit $ EdhBool True
      where
        world = edh'prog'world $ edh'thread'prog ets

    joinProc :: EdhHostProc
    joinProc !exit !ets = withThisHostObj ets $ \ !server ->
      readTMVar (edh'lang'server'eol server) >>= \case
        Left !e ->
          edh'exception'wrapper world e
            >>= \ !exo -> edhThrow ets $ EdhObject exo
        Right () -> exitEdh ets exit nil
      where
        world = edh'prog'world $ edh'thread'prog ets

    stopProc :: EdhHostProc
    stopProc !exit !ets = withThisHostObj ets $ \ !server -> do
      stopped <- tryPutTMVar (edh'lang'server'eol server) $ Right ()
      exitEdh ets exit $ EdhBool stopped
