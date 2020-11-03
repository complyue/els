
module Language.Edh.LS.MicroProto where

import           Prelude
-- import           Debug.Trace

import           Control.Exception
import           Control.Monad.Reader
import           Control.Concurrent
import           Control.Concurrent.STM

import           Data.Hashable
import qualified Data.ByteString               as B
import qualified Data.ByteString.Lazy          as BL
import qualified Data.ByteString.Lazy.Char8    as C
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import qualified Data.Text.Lazy                as TL
import qualified Data.Text.Encoding            as TE
import qualified Data.Text.Lazy.Encoding       as TLE
import           Data.Int

import           Language.Edh.EHI


maxHeaderLength :: Int
maxHeaderLength = 600


type HeaderName = Text
type HeaderContent = Text
type PacketHeaders = [(HeaderName, HeaderContent)]
type PacketContent = B.ByteString
type PacketSink = TMVar Packet
type EndOfStream = TMVar (Either SomeException ())

data Packet = Packet !PacketHeaders !PacketContent
  deriving (Eq, Show)
instance Hashable Packet where
  hashWithSalt s (Packet headers content) =
    s `hashWithSalt` headers `hashWithSalt` content

-- | Construct a textual packet.
textPacket :: PacketHeaders -> Text -> Packet
textPacket !headers !txt = Packet headers $ TE.encodeUtf8 txt


-- | Send out a binary packet.
sendPacket :: (B.ByteString -> IO ()) -> Packet -> IO ()
sendPacket !outletter (Packet !headers !content) = do
  let !pktLen = B.length content
  -- write packet headers
  outletter
    $  TE.encodeUtf8
    $  "Content-Length: "
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
receivePacketStream
  :: Text -> (Int -> IO B.ByteString) -> PacketSink -> EndOfStream -> IO ()
receivePacketStream peerSite !intaker !pktSink !eos = do
  recvThId <- myThreadId -- async kill the receiving action on eos
  void $ forkIO $ atomically (readTMVar eos) >> killThread recvThId
  catch (parsePkts BL.empty)
    -- note this thread can be killed as above due to eos, don't rethrow
    -- here, some informed thread should rethrow the error in eos if any
    -- get recorded there.
    -- here just try mark end-of-stream with the error occurred, i.e.
    -- previous eos state will be reserved if already signaled. and done.
    $ \(e :: SomeException) -> void $ atomically $ tryPutTMVar eos $ Left e
 where

  getExact :: Int64 -> IO (BL.ByteString, B.ByteString)
  getExact !nbytes64 = intaker nbytes >>= \chunk ->
    let more2read = nbytes64 - fromIntegral (B.length chunk)
    in  if more2read > 0
          then getExact more2read >>= \(chunk', readahead) ->
            return (BL.fromStrict chunk <> chunk', readahead)
          else case B.splitAt nbytes chunk of
            (exact, readahead) -> return (BL.fromStrict exact, readahead)
    where nbytes = fromIntegral nbytes64

  parsePkts :: BL.ByteString -> IO ()
  parsePkts !readahead = do
    (contentLen, headers, readahead') <- parseHdrs (-1) [] readahead
    if contentLen < 0
      then -- normal eos, try mark and done
           void $ atomically $ tryPutTMVar eos $ Right ()
      else do
        let (content, rest) = BL.splitAt contentLen readahead'
            more2read       = contentLen - BL.length content
        if more2read > 0
          then do
            (morePayload, moreAhead) <- getExact more2read
            atomically
                (        (Right <$> putTMVar
                           pktSink
                           (Packet headers $ BL.toStrict (content <> morePayload))
                         )
                `orElse` (Left <$> readTMVar eos)
                )
              >>= \case
                    Left  (Left  e ) -> throwIO e
                    Left  (Right ()) -> return ()
                    Right _          -> parsePkts $ BL.fromStrict moreAhead
          else
            atomically
                ((   Right
                 <$> putTMVar pktSink (Packet headers $ BL.toStrict content)
                 )
                `orElse` (Left <$> readTMVar eos)
                )
              >>= \case
                    Left  (Left  e ) -> throwIO e
                    Left  (Right ()) -> return ()
                    Right _          -> parsePkts rest

  parseHdrs
    :: Int64
    -> PacketHeaders
    -> BL.ByteString
    -> IO (Int64, PacketHeaders, BL.ByteString)
  parseHdrs !knownLen !hdrs !readahead = do
    peeked <- if BL.null readahead
      then BL.fromStrict <$> intaker chunkSize
      else return readahead
    if BL.null peeked
      then return (knownLen, hdrs, BL.empty)
      else
        let (!hdrLine, !rest) = C.break (== '\r') peeked
        in  if BL.null rest || BL.null (C.tail rest)
              then if BL.length peeked < fromIntegral maxHeaderLength
                then do
                  morePeek <- BL.fromStrict <$> intaker chunkSize
                  parseHdrs knownLen hdrs $ peeked <> morePeek
                else throwIO
                  $ EdhPeerError peerSite "incoming packet header too long"
              else case C.stripPrefix "\r\n" rest of
                Nothing ->
                  throwIO $ EdhPeerError peerSite "\\r not followed by \\n"
                Just !readahead' -> if BL.null hdrLine
                  then -- reached packet content
                       return (knownLen, hdrs, readahead')
                  else
                    let (!hdrNameBytes, !hdrRest) = C.break (== ':') hdrLine
                    in  case BL.stripPrefix ": " hdrRest of
                          Nothing -> throwIO $ EdhPeerError
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
                            in  parseHdrs knownLen'
                                          ((hdrName, hdrContent) : hdrs)
                                          readahead'

  -- | Considering hardware and network realities, the maximum number of bytes
  -- to receive should be a small power of 2
  chunkSize :: Int
  chunkSize = 4096
