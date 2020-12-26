module Language.Edh.LS.Json where

import Language.Edh.EHI
import Language.Edh.Meta.Model
import Prelude

-- * helper functions converting to json native `EdhValue`s

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

instance ToLSP EL'Diagnostic where
  toLSP
    ( EL'Diagnostic
        !rng
        !severity
        !code
        !source
        !msg
        !tags
      ) =
      jsonObject
        [ ("range", toLSP rng),
          ("severity", jsonInt severity),
          ( "code",
            case code of
              Left !i -> jsonInt i
              Right !s -> EdhString s
          ),
          ("source", EdhString source),
          ("message", EdhString msg),
          ( "tags",
            if null tags
              then nil
              else jsonArray' (EdhDecimal . fromIntegral) tags
          )
        ]

attrUpLinkChain :: EL'AttrDef -> [EdhValue]
attrUpLinkChain !def = case el'attr'def'value def of
  EL'External !fromModu !fromDef ->
    if src'line (src'start $ el'attr'def'focus def) < 0
      then attrUpLinkChain fromDef -- hidden definition
      else
        jsonObject
          [ ("originSelectionRange", toLSP $ el'attr'def'focus def),
            ("targetUri", toLSP $ el'modu'doc fromModu),
            ("targetRange", toLSP $ exprSrcSpan $ el'attr'def'expr fromDef),
            ("targetSelectionRange", toLSP $ el'attr'def'focus fromDef)
          ] :
        attrUpLinkChain fromDef
  _ -> []

instance ToLSP EL'AttrRef where
  toLSP (EL'AttrRef (AttrAddrSrc _ !addr'span) !originModu !def) =
    if src'line (src'start $ el'attr'def'focus def) < 0
      then case el'attr'def'value def of -- hidden definition
        EL'External !fromModu !fromDef ->
          jsonArray $
            jsonObject
              [ ("originSelectionRange", toLSP addr'span),
                ("targetUri", toLSP $ el'modu'doc fromModu),
                ("targetRange", toLSP $ exprSrcSpan $ el'attr'def'expr fromDef),
                ("targetSelectionRange", toLSP $ el'attr'def'focus fromDef)
              ] :
            attrUpLinkChain fromDef
        _ -> jsonArray [] -- hidden yet not pointing to external value
      else
        jsonArray $
          jsonObject
            [ ("originSelectionRange", toLSP addr'span),
              ("targetUri", toLSP $ el'modu'doc originModu),
              ("targetRange", toLSP $ exprSrcSpan $ el'attr'def'expr def),
              ("targetSelectionRange", toLSP $ el'attr'def'focus def)
            ] :
          attrUpLinkChain def
