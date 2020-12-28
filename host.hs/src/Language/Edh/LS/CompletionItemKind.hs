{-# LANGUAGE PatternSynonyms #-}

module Language.Edh.LS.CompletionItemKind where

import Language.Edh.LS.Json
import Prelude

newtype CompletionItemKind = CompletionItemKind Int

pattern Text :: CompletionItemKind
pattern Text = CompletionItemKind 1

pattern Method :: CompletionItemKind
pattern Method = CompletionItemKind 2

pattern Function :: CompletionItemKind
pattern Function = CompletionItemKind 3

pattern Constructor :: CompletionItemKind
pattern Constructor = CompletionItemKind 4

pattern Field :: CompletionItemKind
pattern Field = CompletionItemKind 5

pattern Variable :: CompletionItemKind
pattern Variable = CompletionItemKind 6

pattern Class :: CompletionItemKind
pattern Class = CompletionItemKind 7

pattern Interface :: CompletionItemKind
pattern Interface = CompletionItemKind 8

pattern Module :: CompletionItemKind
pattern Module = CompletionItemKind 9

pattern Property :: CompletionItemKind
pattern Property = CompletionItemKind 10

pattern Unit :: CompletionItemKind
pattern Unit = CompletionItemKind 11

pattern Value :: CompletionItemKind
pattern Value = CompletionItemKind 12

pattern Enum :: CompletionItemKind
pattern Enum = CompletionItemKind 13

pattern Keyword :: CompletionItemKind
pattern Keyword = CompletionItemKind 14

pattern Snippet :: CompletionItemKind
pattern Snippet = CompletionItemKind 15

pattern Color :: CompletionItemKind
pattern Color = CompletionItemKind 16

pattern File :: CompletionItemKind
pattern File = CompletionItemKind 17

pattern Reference :: CompletionItemKind
pattern Reference = CompletionItemKind 18

pattern Folder :: CompletionItemKind
pattern Folder = CompletionItemKind 19

pattern EnumMember :: CompletionItemKind
pattern EnumMember = CompletionItemKind 20

pattern Constant :: CompletionItemKind
pattern Constant = CompletionItemKind 21

pattern Struct :: CompletionItemKind
pattern Struct = CompletionItemKind 22

pattern Event :: CompletionItemKind
pattern Event = CompletionItemKind 23

pattern Operator :: CompletionItemKind
pattern Operator = CompletionItemKind 24

pattern TypeParameter :: CompletionItemKind
pattern TypeParameter = CompletionItemKind 25

instance ToLSP CompletionItemKind where
  toLSP (CompletionItemKind n) = jsonInt n
