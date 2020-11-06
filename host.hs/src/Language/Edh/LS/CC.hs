
module Language.Edh.LS.CC where

import           Prelude
-- import           Debug.Trace

import           Control.Exception
import           Control.Monad
import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Maybe
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Text.Encoding
import           Data.Dynamic

import           Network.Socket
import           Network.Socket.ByteString      ( recv
                                                , sendAll
                                                )

import           Language.Edh.EHI

import           Language.Edh.LS.MicroProto


type LangClntAddr = Text
type LangClntPort = Int

-- | Network connection to a languageserver client
data CC = CC {
    -- the import spec of the module to run as the service
      cc'modu :: !Text
    -- local network port to bind
    , cc'client'port :: !LangClntPort
    -- local network interface to bind
    , cc'client'addr :: !LangClntAddr
    -- actually connected network addresses
    , cc'client'addrs :: !(TMVar [AddrInfo])
    -- end-of-life status
    , cc'eol :: !(TMVar (Either SomeException ()))
    -- service module initializer, must callable if not nil
    , cc'init :: !EdhValue
  }


createCCClass :: Object -> Scope -> STM Object
createCCClass !addrClass !clsOuterScope =
  mkHostClass clsOuterScope "CC" (allocEdhObj ccAllocator) [] $ \ !clsScope ->
    do
      !mths <- sequence
        [ (AttrByName nm, ) <$> mkHostProc clsScope vc nm hp
        | (nm, vc, hp) <-
          [ ("addrs"   , EdhMethod, wrapHostProc addrsProc)
          , ("eol"     , EdhMethod, wrapHostProc eolProc)
          , ("join"    , EdhMethod, wrapHostProc joinProc)
          , ("stop"    , EdhMethod, wrapHostProc stopProc)
          , ("__repr__", EdhMethod, wrapHostProc reprProc)
          ]
        ]
      iopdUpdate mths $ edh'scope'entity clsScope

 where

  -- | host constructor CC()
  ccAllocator
    :: "service" !: Text
    -> "port" !: Int
    -> "addr" ?: Text
    -> "init" ?: EdhValue
    -> EdhObjectAllocator
  ccAllocator (mandatoryArg -> !service) (mandatoryArg -> !ctorPort) (defaultArg "127.0.0.1" -> !ctorAddr) (defaultArg nil -> !init_) !ctorExit !etsCtor
    = if edh'in'tx etsCtor
      then throwEdh etsCtor
                    UsageError
                    "you don't create network objects within a transaction"
      else case edhUltimate init_ of
        EdhNil                               -> withInit nil
        mth@(EdhProcedure EdhMethod{} _    ) -> withInit mth
        mth@(EdhBoundProc EdhMethod{} _ _ _) -> withInit mth
        !badInit -> edhValueDesc etsCtor badInit $ \ !badDesc ->
          throwEdh etsCtor UsageError $ "invalid init: " <> badDesc
   where
    withInit !__modu_init__ = do
      serviceAddrs <- newEmptyTMVar
      svcEoL       <- newEmptyTMVar
      let !cc = CC { cc'modu         = service
                   , cc'client'port  = fromIntegral ctorPort
                   , cc'client'addr  = ctorAddr
                   , cc'client'addrs = serviceAddrs
                   , cc'eol          = svcEoL
                   , cc'init         = __modu_init__
                   }
      runEdhTx etsCtor $ edhContIO $ do
        void $ forkFinally
          (serviceThread cc)
          ( void
          . atomically
            -- fill empty addrs if the connection has ever failed
          . (tryPutTMVar serviceAddrs [] <*)
            -- mark service end-of-life anyway finally
          . tryPutTMVar svcEoL
          )
        atomically $ ctorExit $ HostStore (toDyn cc)

    serviceThread :: CC -> IO ()
    serviceThread (CC !svcModu !servPort !servAddr !serviceAddrs !svcEoL !__modu_init__)
      = do
        addr <- resolveServAddr
        bracket
            (socket (addrFamily addr) (addrSocketType addr) (addrProtocol addr))
            close
          $ \sock -> do
              connect sock $ addrAddress addr
              srvAddr <- getPeerName sock
              atomically
                $   fromMaybe []
                <$> tryTakeTMVar serviceAddrs
                >>= putTMVar serviceAddrs
                .   (addr :)
              try (servLanguageClient (T.pack $ show srvAddr) sock)
                >>= (gracefulClose sock 5000 <*)
                .   atomically
                .   tryPutTMVar svcEoL

     where
      ctx             = edh'context etsCtor
      world           = edh'ctx'world ctx

      resolveServAddr = do
        let hints =
              defaultHints { addrFlags = [AI_PASSIVE], addrSocketType = Stream }
        addr : _ <- getAddrInfo (Just hints)
                                (Just $ T.unpack servAddr)
                                (Just (show servPort))
        return addr

      servLanguageClient :: Text -> Socket -> IO ()
      servLanguageClient !clientId !sock = do
        !pktSink <- newEmptyTMVarIO
        !poq     <- newEmptyTMVarIO

        let
          ccEoLProc :: EdhHostProc
          ccEoLProc !exit !ets = tryReadTMVar svcEoL >>= \case
            Nothing        -> exitEdh ets exit $ EdhBool False
            Just (Left !e) -> edh'exception'wrapper world e
              >>= \ !exo -> exitEdh ets exit $ EdhObject exo
            Just (Right ()) -> exitEdh ets exit $ EdhBool True

          recvOnePktProc :: Scope -> EdhHostProc
          recvOnePktProc !sandbox !exit !ets =
            takeTMVar pktSink >>= \(Packet _headers !content) -> do
              -- interpret the content as command, return as is
              let !src = decodeUtf8 content
              runEdhInSandbox ets sandbox (evalEdh (T.unpack clientId) src)
                $ \ !r _ets -> exitEdh ets exit r

          postOnePktProc :: "rpcOut" !: Text -> RestKwArgs -> EdhHostProc
          postOnePktProc (mandatoryArg -> !content) !headers !exit !ets = go
            (odToList headers)
            []
           where
            go
              :: [(AttrKey, EdhValue)]
              -> [(HeaderName, HeaderContent)]
              -> STM ()
            go [] !hdrs = do
              void $ tryPutTMVar poq $ textPacket hdrs content
              exitEdh ets exit nil
            go ((k, v) : rest) !hdrs =
              edhValueStr ets v $ \ !sv -> go rest ((attrKeyStr k, sv) : hdrs)

          prepService :: EdhModulePreparation
          prepService !etsModu !exit =
            mkSandbox etsModu moduObj $ \ !sandboxScope -> do

              -- define and implant procedures to the module being prepared
              !moduMths <- sequence
                [ (AttrByName nm, ) <$> mkHostProc moduScope vc nm hp
                | (nm, vc, hp) <-
                  [ ("eol", EdhMethod, wrapHostProc ccEoLProc)
                  , ( "recvOnePkt"
                    , EdhMethod
                    , wrapHostProc $ recvOnePktProc sandboxScope
                    )
                  , ("postOnePkt", EdhMethod, wrapHostProc postOnePktProc)
                  ]
                ]
              let !moduArts =
                    (AttrByName "clientId", EdhString clientId) : moduMths
              iopdUpdate moduArts $ edh'scope'entity moduScope

              -- call the service module initialization method in the module
              -- context (where both contextual this/that are the module object)
              if __modu_init__ == nil
                then exit
                else
                  edhPrepareCall'
                      etsModu
                      __modu_init__
                      (ArgsPack [EdhObject $ edh'scope'this moduScope] odEmpty)
                    $ \ !mkCall -> runEdhTx etsModu $ mkCall $ \_result _ets ->
                        exit
           where
            !moduScope = contextScope $ edh'context etsModu
            !moduObj   = edh'scope'this moduScope

        void
          -- run the service module as another program
          $ forkFinally (runEdhModule' world (T.unpack svcModu) prepService)
          -- mark client end-of-life with the result anyway
          $ void
          . atomically
          . tryPutTMVar svcEoL
          . void

        -- pump commands in, 
        -- make this thread the only one reading the handle
        -- note this won't return, will be asynchronously killed on eol
        void $ forkIO $ receivePacketStream clientId (recv sock) pktSink svcEoL

        let
          serializeCmdsOut :: IO ()
          serializeCmdsOut =
            atomically
                ((Right <$> takeTMVar poq) `orElse` (Left <$> readTMVar svcEoL))
              >>= \case
                    Left _ -> return ()
                    Right !pkt ->
                      catch (sendPacket (sendAll sock) pkt >> serializeCmdsOut)
                        $ \(e :: SomeException) -> -- mark eol on error
                            atomically $ void $ tryPutTMVar svcEoL $ Left e
        -- pump commands out,
        -- make this thread the only one writing the handle
        serializeCmdsOut


  reprProc :: EdhHostProc
  reprProc !exit !ets =
    withThisHostObj ets $ \(CC !service !port !addr _ _ _) ->
      exitEdh ets exit
        $  EdhString
        $  "CC("
        <> T.pack (show service)
        <> ", "
        <> T.pack (show port)
        <> ", "
        <> T.pack (show addr)
        <> ")"

  addrsProc :: EdhHostProc
  addrsProc !exit !ets = withThisHostObj ets
    $ \ !client -> readTMVar (cc'client'addrs client) >>= wrapAddrs []
   where
    wrapAddrs :: [EdhValue] -> [AddrInfo] -> STM ()
    wrapAddrs addrs [] =
      exitEdh ets exit $ EdhArgsPack $ ArgsPack addrs odEmpty
    wrapAddrs !addrs (addr : rest) = edhCreateHostObj addrClass (toDyn addr) []
      >>= \ !addrObj -> wrapAddrs (EdhObject addrObj : addrs) rest

  eolProc :: EdhHostProc
  eolProc !exit !ets = withThisHostObj ets $ \ !client ->
    tryReadTMVar (cc'eol client) >>= \case
      Nothing        -> exitEdh ets exit $ EdhBool False
      Just (Left !e) -> edh'exception'wrapper world e
        >>= \ !exo -> exitEdh ets exit $ EdhObject exo
      Just (Right ()) -> exitEdh ets exit $ EdhBool True
    where world = edh'ctx'world $ edh'context ets

  joinProc :: EdhHostProc
  joinProc !exit !ets = withThisHostObj ets $ \ !client ->
    readTMVar (cc'eol client) >>= \case
      Left !e ->
        edh'exception'wrapper world e >>= \ !exo -> edhThrow ets $ EdhObject exo
      Right () -> exitEdh ets exit nil
    where world = edh'ctx'world $ edh'context ets

  stopProc :: EdhHostProc
  stopProc !exit !ets = withThisHostObj ets $ \ !client -> do
    stopped <- tryPutTMVar (cc'eol client) $ Right ()
    exitEdh ets exit $ EdhBool stopped

