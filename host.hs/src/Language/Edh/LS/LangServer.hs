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
    edh'lang'service :: !EdhValue,
    -- the world in which the service will run
    edh'lang'service'world :: !EdhWorld,
    -- local network port to bind
    edh'lang'server'port :: !PortNumber,
    -- max port number to try bind
    edh'lang'server'port'max :: !PortNumber,
    -- local network interface to bind
    edh'lang'server'addr :: !Text,
    -- actually listened network addresses
    edh'lang'serving'addrs :: !(TMVar [AddrInfo]),
    -- end-of-life status
    edh'lang'server'eol :: !(TMVar (Either SomeException ()))
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
      "service" !: EdhValue ->
      "port" ?: Int ->
      "port'max" ?: Int ->
      "addr" ?: Text ->
      EdhObjectAllocator
    serverAllocator
      (mandatoryArg -> !service)
      (defaultArg 1707 -> !ctorPort)
      (defaultArg ctorPort -> port'max)
      (defaultArg "127.0.0.1" -> !ctorAddr)
      !ctorExit
      !etsCtor = do
            !servAddrs <- newEmptyTMVar
            !servEoL <- newEmptyTMVar
            let !server =
                  LangServer
                    { edh'lang'service = service,
                      edh'lang'service'world =
                        edh'prog'world $ edh'thread'prog etsCtor,
                      edh'lang'server'port = fromIntegral ctorPort,
                      edh'lang'server'port'max = fromIntegral port'max,
                      edh'lang'server'addr = ctorAddr,
                      edh'lang'serving'addrs = servAddrs,
                      edh'lang'server'eol = servEoL
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
        where
          serverThread :: LangServer -> IO ()
          serverThread
            ( LangServer
                !servProc
                !servWorld
                !servPort
                !portMax
                !servAddr
                !servAddrs
                !servEoL
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
                            edh'exception'wrapper world (Just ets) e
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
                                (Just ets)
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

                      edhHandler = pushEdhStack $ \ !etsEffs ->
                        -- prepare a dedicated scope atop world root scope, with els effects
                        -- implanted, then call the configured service procedure from there
                        let effsScope = contextScope $ edh'context etsEffs
                         in mkScopeSandbox etsEffs effsScope $ \ !sandboxScope -> do
                              !effMths <-
                                sequence
                                  [ (AttrByName nm,) <$> mkHostProc effsScope vc nm hp
                                    | (nm, vc, hp) <-
                                        [ ("eol", EdhMethod, wrapHostProc ccEoLProc),
                                          ( "recvOnePkt",
                                            EdhMethod,
                                            wrapHostProc $ recvOnePktProc sandboxScope
                                          ),
                                          ("postOnePkt", EdhMethod, wrapHostProc postOnePktProc)
                                        ]
                                  ]
                              let !effArts = (AttrByName "clientId", EdhString clientId) : effMths
                              prepareEffStore etsEffs (edh'scope'entity effsScope)
                                >>= iopdUpdate effArts

                              runEdhTx etsEffs $ edhMakeCall servProc [] haltEdhProgram

                  -- run the service procedure on a separate thread as another Edh program
                  --
                  -- this implements structured concurrency per client connection,
                  -- i.e. all Edh threads spawned by this client will terminate upon its
                  -- disconnection, while resource cleanups should be scheduled via defer
                  -- mechanism, or exception handling, that expecting `ThreadTerminate` to be
                  -- thrown, the cleanup action is usually in a finally block in this way
                  void $
                    forkFinally (runEdhProgram' servWorld edhHandler) $
                      -- mark client end-of-life with the result anyway
                      void . atomically . tryPutTMVar clientEoL . void

                  -- pump commands in, make this thread the only one reading the handle
                  -- note this won't return, will be asynchronously killed on eol
                  void $
                    forkFinally
                      (receiveRpcStream clientId (recv sock) pktSink clientEoL)
                      -- mark client end-of-life upon disconnected or err out
                      $ void . atomically . tryPutTMVar clientEoL . void

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
      withThisHostObj ets $ \(LangServer _ _ !port !port'max !addr _ _) ->
        exitEdh ets exit $
          EdhString $
            "LangServer<port= "
              <> T.pack (show port)
              <> ", port'max= "
              <> T.pack (show port'max)
              <> ", addr= "
              <> T.pack (show addr)
              <> ">"

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
          edh'exception'wrapper world (Just ets) e
            >>= \ !exo -> exitEdh ets exit $ EdhObject exo
        Just (Right ()) -> exitEdh ets exit $ EdhBool True
      where
        world = edh'prog'world $ edh'thread'prog ets

    joinProc :: EdhHostProc
    joinProc !exit !ets = withThisHostObj ets $ \ !server ->
      readTMVar (edh'lang'server'eol server) >>= \case
        Left !e ->
          edh'exception'wrapper world (Just ets) e
            >>= \ !exo -> edhThrow ets $ EdhObject exo
        Right () -> exitEdh ets exit nil
      where
        world = edh'prog'world $ edh'thread'prog ets

    stopProc :: EdhHostProc
    stopProc !exit !ets = withThisHostObj ets $ \ !server -> do
      stopped <- tryPutTMVar (edh'lang'server'eol server) $ Right ()
      exitEdh ets exit $ EdhBool stopped
