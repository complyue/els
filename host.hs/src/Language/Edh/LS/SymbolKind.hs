{-# LANGUAGE PatternSynonyms #-}

module Language.Edh.LS.SymbolKind where

import Language.Edh.LS.Json
import Prelude

newtype SymbolKind = SymbolKind Int

pattern File :: SymbolKind
pattern File = SymbolKind 1

pattern Module :: SymbolKind
pattern Module = SymbolKind 2

pattern Namespace :: SymbolKind
pattern Namespace = SymbolKind 3

pattern Package :: SymbolKind
pattern Package = SymbolKind 4

pattern Class :: SymbolKind
pattern Class = SymbolKind 5

pattern Method :: SymbolKind
pattern Method = SymbolKind 6

pattern Property :: SymbolKind
pattern Property = SymbolKind 7

pattern Field :: SymbolKind
pattern Field = SymbolKind 8

pattern Constructor :: SymbolKind
pattern Constructor = SymbolKind 9

pattern Enum :: SymbolKind
pattern Enum = SymbolKind 10

pattern Interface :: SymbolKind
pattern Interface = SymbolKind 11

pattern Function :: SymbolKind
pattern Function = SymbolKind 12

pattern Variable :: SymbolKind
pattern Variable = SymbolKind 13

pattern Constant :: SymbolKind
pattern Constant = SymbolKind 14

pattern String :: SymbolKind
pattern String = SymbolKind 15

pattern Number :: SymbolKind
pattern Number = SymbolKind 16

pattern Boolean :: SymbolKind
pattern Boolean = SymbolKind 17

pattern Array :: SymbolKind
pattern Array = SymbolKind 18

pattern Object :: SymbolKind
pattern Object = SymbolKind 19

pattern Key :: SymbolKind
pattern Key = SymbolKind 20

pattern Null :: SymbolKind
pattern Null = SymbolKind 21

pattern EnumMember :: SymbolKind
pattern EnumMember = SymbolKind 22

pattern Struct :: SymbolKind
pattern Struct = SymbolKind 23

pattern Event :: SymbolKind
pattern Event = SymbolKind 24

pattern Operator :: SymbolKind
pattern Operator = SymbolKind 25

pattern TypeParameter :: SymbolKind
pattern TypeParameter = SymbolKind 26

instance ToLSP SymbolKind where
  toLSP (SymbolKind n) = jsonInt n
