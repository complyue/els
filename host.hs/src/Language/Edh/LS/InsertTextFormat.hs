{-# LANGUAGE PatternSynonyms #-}

module Language.Edh.LS.InsertTextFormat where

import Language.Edh.LS.Json
import Prelude

newtype InsertTextFormat = InsertTextFormat Int

pattern PlainText :: InsertTextFormat
pattern PlainText = InsertTextFormat 1

pattern Snippet :: InsertTextFormat
pattern Snippet = InsertTextFormat 2

instance ToLSP InsertTextFormat where
  toLSP (InsertTextFormat n) = jsonInt n
