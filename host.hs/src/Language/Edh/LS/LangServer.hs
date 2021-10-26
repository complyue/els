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
import Language.Edh.LS.BaseLSP
import Language.Edh.EHI
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

createLangServerClass :: Object -> Edh Object
createLangServerClass !addrClass =
  mkEdhClass "LangServer" (allocObjM serverAllocator) [] $ do
    !mths <-
      sequence $
        [ (AttrByName nm,) <$> mkEdhProc vc nm hp
          | (nm, vc, hp) <-
              [ ("addrs", EdhMethod, wrapEdhProc addrsProc),
                ("eol", EdhMethod, wrapEdhProc eolProc),
                ("join", EdhMethod, wrapEdhProc joinProc),
                ("stop", EdhMethod, wrapEdhProc stopProc),
                ("__repr__", EdhMethod, wrapEdhProc reprProc)
              ]
        ]

    !clsScope <- contextScope . edh'context <$> edhThreadState
    iopdUpdateEdh mths $ edh'scope'entity clsScope
  where
    serverAllocator ::
      "service" !: EdhValue ->
      "port" ?: Int ->
      "port'max" ?: Int ->
      "addr" ?: Text ->
      Edh (Maybe Unique, ObjectStore)
    serverAllocator
      (mandatoryArg -> !service)
      (defaultArg 1707 -> !ctorPort)
      (defaultArg ctorPort -> port'max)
      (defaultArg "127.0.0.1" -> !ctorAddr) = do
        !world <- edh'prog'world <$> edhProgramState
        !server <- inlineSTM $ do
          !servAddrs <- newEmptyTMVar
          !servEoL <- newEmptyTMVar
          return
            LangServer
              { edh'lang'service = service,
                edh'lang'service'world = world,
                edh'lang'server'port = fromIntegral ctorPort,
                edh'lang'server'port'max = fromIntegral port'max,
                edh'lang'server'addr = ctorAddr,
                edh'lang'serving'addrs = servAddrs,
                edh'lang'server'eol = servEoL
              }
        afterTxIO $ do
          void $
            forkFinally
              (serverThread server)
              ( atomically
                  . void
                  -- fill empty addrs if the connection has ever failed
                  . (tryPutTMVar (edh'lang'serving'addrs server) [] <*)
                  -- mark server end-of-life anyway finally
                  . void
                  . tryPutTMVar (edh'lang'server'eol server)
              )
        return (Nothing, HostStore (toDyn server))
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

                  let ccEoLProc :: Edh EdhValue
                      ccEoLProc =
                        inlineSTM (tryReadTMVar clientEoL) >>= \case
                          Nothing -> return $ EdhBool False
                          Just (Left !e) -> throwHostM e
                          Just (Right ()) -> return $ EdhBool True

                      recvOnePktProc :: Scope -> Edh EdhValue
                      recvOnePktProc !sandbox =
                        inlineSTM
                          ( (Right <$> takeTMVar pktSink)
                              `orElse` (Left <$> readTMVar clientEoL)
                          )
                          >>= \case
                            -- reached normal end-of-stream
                            Left Right {} -> return nil
                            -- previously eol due to error
                            Left (Left !ex) -> throwHostM ex
                            Right (Rpc _headers !content) -> do
                              -- interpret the content as command, return as is
                              let !src = decodeUtf8 content
                              runInSandboxM
                                sandbox
                                (evalSrcM ("lsc:" <> clientId) src)

                      postOnePktProc ::
                        "rpcOut" !: Text ->
                        RestKwArgs ->
                        Edh EdhValue
                      postOnePktProc
                        (mandatoryArg -> !content)
                        !headers = go (odToList headers) []
                          where
                            go ::
                              [(AttrKey, EdhValue)] ->
                              [(HeaderName, HeaderContent)] ->
                              Edh EdhValue
                            go [] !hdrs = do
                              void $ tryPutTMVarEdh poq $ textRpc hdrs content
                              return nil
                            go ((k, v) : rest) !hdrs =
                              edhValueStrM v >>= \ !sv ->
                                go rest ((attrKeyStr k, sv) : hdrs)

                      edhHandler = pushStackM $ do
                        -- prepare a dedicated scope atop world root scope,
                        -- with provisioned effects implanted, then call the
                        -- configured service procedure from there
                        !effsScope <-
                          contextScope . edh'context <$> edhThreadState
                        !sandbox <- mkSandboxM effsScope

                        !effMths <-
                          sequence
                            [ (AttrByName nm,) <$> mkEdhProc vc nm hp
                              | (nm, vc, hp) <-
                                  [ ("eol", EdhMethod, wrapEdhProc ccEoLProc),
                                    ( "recvOnePkt",
                                      EdhMethod,
                                      wrapEdhProc $ recvOnePktProc sandbox
                                    ),
                                    ("postOnePkt", EdhMethod, wrapEdhProc postOnePktProc)
                                  ]
                            ]
                        let !effArts = (AttrByName "clientId", EdhString clientId) : effMths

                        prepareEffStoreM >>= iopdUpdateEdh effArts
                        callM servProc []

                  -- run the service procedure on a separate thread as another Edh program
                  --
                  -- this implements structured concurrency per client connection,
                  -- i.e. all Edh threads spawned by this client will terminate upon its
                  -- disconnection, while resource cleanups should be scheduled via defer
                  -- mechanism, or exception handling, that expecting `ThreadTerminate` to be
                  -- thrown, the cleanup action is usually in a finally block in this way
                  void $
                    forkFinally (runProgramM' servWorld edhHandler) $
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

    withThisServer :: forall r. (Object -> LangServer -> Edh r) -> Edh r
    withThisServer withServer = do
      !this <- edh'scope'this . contextScope . edh'context <$> edhThreadState
      case fromDynamic =<< dynamicHostData this of
        Nothing -> throwEdhM EvalError "bug: this is not an Server"
        Just !col -> withServer this col

    reprProc :: Edh EdhValue
    reprProc = withThisServer $
      \_this (LangServer _ _ !port !port'max !addr _ _) ->
        return $
          EdhString $
            "LangServer<port= "
              <> T.pack (show port)
              <> ", port'max= "
              <> T.pack (show port'max)
              <> ", addr= "
              <> T.pack (show addr)
              <> ">"

    addrsProc :: Edh EdhValue
    addrsProc = withThisServer $ \_this !server ->
      inlineSTM (readTMVar $ edh'lang'serving'addrs server) >>= wrapAddrs []
      where
        wrapAddrs :: [EdhValue] -> [AddrInfo] -> Edh EdhValue
        wrapAddrs addrs [] =
          return $ EdhArgsPack $ ArgsPack addrs odEmpty
        wrapAddrs !addrs (addr : rest) =
          createHostObjectM addrClass addr
            >>= \ !addrObj -> wrapAddrs (EdhObject addrObj : addrs) rest

    eolProc :: Edh EdhValue
    eolProc = withThisServer $ \_this !server ->
      inlineSTM (tryReadTMVar $ edh'lang'server'eol server) >>= \case
        Nothing -> return $ EdhBool False
        Just (Left !e) -> throwHostM e
        Just (Right ()) -> return $ EdhBool True

    joinProc :: Edh EdhValue
    joinProc = withThisServer $ \_this !server ->
      inlineSTM (readTMVar $ edh'lang'server'eol server) >>= \case
        Left !e -> throwHostM e
        Right () -> return nil

    stopProc :: Edh EdhValue
    stopProc = withThisServer $ \_this !server ->
      inlineSTM $
        fmap EdhBool $
          tryPutTMVar (edh'lang'server'eol server) $ Right ()
