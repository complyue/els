module Language.Edh.LS.Json where

import Language.Edh.MHI
import Prelude

-- * helper functions converting arbitrary value to json native `EdhValue`

jsonNull :: EdhValue
jsonNull = EdhNamedValue "null" EdhNil

jsonArray :: [EdhValue] -> EdhValue
jsonArray !xs = EdhArgsPack $ ArgsPack xs odEmpty

jsonArray' :: forall a. (a -> EdhValue) -> [a] -> EdhValue
jsonArray' !c !xs = jsonArray $ c <$> xs

jsonObject :: [(AttrName, EdhValue)] -> EdhValue
jsonObject !es = EdhArgsPack $
  ArgsPack [] $ odFromList $ (<$> es) $ \(!n, !v) -> (AttrByName n, v)

jsonObject' :: forall a. (a -> EdhValue) -> [(AttrName, a)] -> EdhValue
jsonObject' !c !es = jsonObject $ (<$> es) $ \(!n, !v) -> (n, c v)

jsonInt :: Integral n => n -> EdhValue
jsonInt = EdhDecimal . fromIntegral

-- * the class for types convertible to json native `EdhValue`s per LSP

class ToLSP t where
  toLSP :: t -> EdhValue

-- * instances converting various types to LSP representation

instance ToLSP a => ToLSP [a] where
  toLSP = jsonArray . fmap toLSP

instance ToLSP SrcPos where
  toLSP (SrcPos !line !char) =
    jsonObject'
      (EdhDecimal . fromIntegral . max 0)
      [("line", line), ("character", char)]

instance ToLSP SrcRange where
  toLSP (SrcRange !start !end) =
    jsonObject [("start", toLSP start), ("end", toLSP end)]

instance ToLSP SrcDoc where
  toLSP (SrcDoc !file) = EdhString $ "file://" <> file

instance ToLSP SrcLoc where
  toLSP (SrcLoc !doc !rng) =
    jsonObject [("uri", toLSP doc), ("range", toLSP rng)]
