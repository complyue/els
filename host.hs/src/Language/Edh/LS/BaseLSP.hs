module Language.Edh.LS.BaseLSP where

-- import           Debug.Trace

import Control.Concurrent
import Control.Concurrent.STM
import Control.Exception
import Control.Monad
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as C
import Data.Hashable
import Data.Int
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TLE
import Language.Edh.EHI
import Prelude

maxHeaderLength :: Int
maxHeaderLength = 600

type HeaderName = Text

type HeaderContent = Text

type RpcHeaders = [(HeaderName, HeaderContent)]

type RpcContent = B.ByteString

type RpcSink = TMVar Rpc

type StreamResult = TMVar (Either SomeException ())

data Rpc = Rpc !RpcHeaders !RpcContent
  deriving (Eq, Show)

instance Hashable Rpc where
  hashWithSalt s (Rpc headers content) =
    s `hashWithSalt` headers `hashWithSalt` content

-- | Construct a textual packet.
textRpc :: RpcHeaders -> Text -> Rpc
textRpc !headers !txt = Rpc headers $ TE.encodeUtf8 txt

-- | Send out a binary packet.
sendRpc :: (B.ByteString -> IO ()) -> Rpc -> IO ()
sendRpc !outletter (Rpc !headers !content) = do
  let !pktLen = B.length content
  -- write packet headers
  outletter $
    TE.encodeUtf8 $
      "Content-Length: "
        <> T.pack (show pktLen)
        <> "\r\n"
  forM_ headers $ \(hdrName, hdrContent) ->
    outletter $ TE.encodeUtf8 $ hdrName <> ": " <> hdrContent <> "\r\n"
  -- header/content separator
  outletter $ TE.encodeUtf8 "\r\n"
  -- write packet content
  outletter content

-- | Receive all packets being streamed to the specified (socket) handle,
-- or have been streamed into a file then have the specified handle
-- opened that file for read.
--
-- Note this should be forked to run in a dedicated thread, that without
-- subsequent actions to perform, as this function will kill its thread
-- asynchronously on eos by design, in lacking of an otherwise better way
-- to cancel reading from the handle.
--
-- Reading of the stream will only flow when packets are taken away from
-- the sink concurrently, and back-pressure will be created by not taking
-- packets away too quickly.
--
-- The caller is responsible to close the handle anyway appropriate, but
-- only after eos is signaled.
receiveRpcStream ::
  Text -> (Int -> IO B.ByteString) -> RpcSink -> StreamResult -> IO ()
receiveRpcStream peerSite !intaker !pktSink !eos = do
  !recvThId <- myThreadId -- async kill the receiving action on eos
  void $ forkIO $ atomically (readTMVar eos) >> killThread recvThId
  -- note this thread can be killed as above due to eos, don't rethrow
  -- here, some informed thread should rethrow the error in eos if any
  -- get recorded there.
  -- here just try mark end-of-stream with the error occurred, i.e.
  -- previous eos state will be reserved if already signaled. and done.
  catch (parsePkts BL.empty) $
    \(e :: SomeException) -> void $ atomically $ tryPutTMVar eos $ Left e
  where
    getExact :: Int64 -> IO (BL.ByteString, B.ByteString)
    getExact !nbytes64 =
      intaker nbytes >>= \ !chunk ->
        let !more2read = nbytes64 - fromIntegral (B.length chunk)
         in if more2read > 0
              then
                if B.null chunk
                  then throwIO $ EdhPeerError peerSite "premature disconnection"
                  else
                    getExact more2read >>= \(!chunk', !readahead) ->
                      return (BL.fromStrict chunk <> chunk', readahead)
              else case B.splitAt nbytes chunk of
                (!exact, !readahead) -> return (BL.fromStrict exact, readahead)
      where
        !nbytes = fromIntegral nbytes64

    parsePkts :: BL.ByteString -> IO ()
    parsePkts !readahead = do
      (!contentLen, !headers, !readahead') <- parseHdrs (-1) [] readahead
      if contentLen < 0
        then
          if null headers && BL.null readahead
            then -- normal eos, try mark and done
              void $ atomically $ tryPutTMVar eos $ Right ()
            else throwIO $ EdhPeerError peerSite "missing Content-Length header"
        else do
          let (!content, !rest) = BL.splitAt contentLen readahead'
              !more2read = contentLen - BL.length content
          if more2read > 0
            then do
              (morePayload, moreAhead) <- getExact more2read
              atomically
                ( ( Right
                      <$> putTMVar
                        pktSink
                        (Rpc headers $ BL.toStrict (content <> morePayload))
                  )
                    `orElse` (Left <$> readTMVar eos)
                )
                >>= \case
                  Left (Left e) -> throwIO e
                  Left (Right ()) -> return ()
                  Right _ -> parsePkts $ BL.fromStrict moreAhead
            else
              atomically
                ( ( Right <$> putTMVar pktSink (Rpc headers $ BL.toStrict content)
                  )
                    `orElse` (Left <$> readTMVar eos)
                )
                >>= \case
                  Left (Left e) -> throwIO e
                  Left (Right ()) -> return ()
                  Right _ -> parsePkts rest

    parseHdrs ::
      Int64 ->
      RpcHeaders ->
      BL.ByteString ->
      IO (Int64, RpcHeaders, BL.ByteString)
    parseHdrs !knownLen !hdrs !readahead = do
      !peeked <-
        if BL.null readahead
          then BL.fromStrict <$> intaker chunkSize
          else return readahead
      if BL.null peeked
        then return (knownLen, hdrs, BL.empty)
        else
          let (!hdrLine, !rest) = C.break (== '\r') peeked
           in if BL.null rest || BL.null (C.tail rest)
                then
                  if BL.length peeked < fromIntegral maxHeaderLength
                    then do
                      !morePeek <- BL.fromStrict <$> intaker chunkSize
                      if BL.null morePeek
                        then
                          throwIO $
                            EdhPeerError peerSite "premature disconnection"
                        else parseHdrs knownLen hdrs $ peeked <> morePeek
                    else
                      throwIO $
                        EdhPeerError peerSite "incoming packet header too long"
                else case C.stripPrefix "\r\n" rest of
                  Nothing ->
                    throwIO $ EdhPeerError peerSite "\\r not followed by \\n"
                  Just !readahead' ->
                    if BL.null hdrLine
                      then -- reached packet content
                        return (knownLen, hdrs, readahead')
                      else
                        let (!hdrNameBytes, !hdrRest) = C.break (== ':') hdrLine
                         in case BL.stripPrefix ": " hdrRest of
                              Nothing ->
                                throwIO $
                                  EdhPeerError
                                    peerSite
                                    "missing header field separator (: )"
                              Just !hdrContentBytes ->
                                let !hdrName =
                                      TL.toStrict $ TLE.decodeUtf8 hdrNameBytes
                                    !hdrContent =
                                      TL.toStrict $ TLE.decodeUtf8 hdrContentBytes
                                    !knownLen' = case hdrName of
                                      "Content-Length" ->
                                        read $ T.unpack hdrContent
                                      _ -> knownLen
                                 in parseHdrs
                                      knownLen'
                                      ((hdrName, hdrContent) : hdrs)
                                      readahead'
    chunkSize :: Int
    chunkSize = 4096
