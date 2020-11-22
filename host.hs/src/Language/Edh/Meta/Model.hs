module Language.Edh.Meta.Model where

-- import           Debug.Trace

import Control.Concurrent.STM
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.Hashable
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Language.Edh.EHI
import Language.Edh.RtTypes
import Prelude

data EL'Home = EL'Home
  { -- | each parent dir of `edh_modules` is considered an Edh home
    --
    -- an Edh home's path should always be absolute and as canonical as possible
    el'home'path :: !Text,
    -- | loaded modules under this home
    --
    -- module name is path (with `.edh` and `/__init__.edh` stripped off), and
    -- relative to the `edh_modules` dir
    --
    -- special case is `/__main__.edh`, from which `.edh` is stripped off, but
    -- the `__main__` part remains in the module name
    el'home'modules :: !(TMVar (Map.HashMap ModuleName EL'ModuSlot))
    -- todo cache configurations per Edh home with more fields
  }

instance Eq EL'Home where
  (EL'Home !x'path _) == (EL'Home !y'path _) = x'path == y'path

type ModuleName = Text

data EL'ModuSlot
  = EL'ModuLoaded !EL'Module
  | EL'ModuLoading ![StmtSrc]
  | EL'ModuFailed !EdhValue

-- | Edh module and `.edh` text doc (os file, virtual or physical, local or
-- remote) be of 1:1 mapping
data EL'Module = EL'Module
  { -- | each parent dir of `edh_modules` is considered an Edh home
    el'modu'home :: !EL'Home,
    -- | absolute path of the `.edh` src file
    el'modu'doc :: !SrcDoc,
    -- | there will be nested scopes appearing in natural source order, within
    -- this root scope of the module
    el'modu'scope :: !EL'Scope,
    -- | an attribute is exported by any form of assignment targeting
    -- current scope, or any form of procedure declaration, which follows an
    -- `export` keyword, or within a block following an `export` keyword
    el'modu'exports :: !EL'Exports
  }

-- | the dict of artifacts by attribute key, for those exported from an object
-- (a module object or vanilla object), with their order of export preserved
--
-- note re-exported values will have their original module preserved
type EL'Exports = OrderedDict EL'AttrKey EL'OriginalValue

data EL'OriginalValue = EL'OriginalValue
  { -- | the original module defined this value
    el'origin'module :: !EL'Module,
    -- TODO will this be useful ?
    -- el'origin'eff'span :: !SrcRange,
    el'value :: !EL'Value
  }

data EL'AttrKey = EL'AttrKey
  { el'akey'src :: !AttrAddrSrc,
    el'akey'reified :: !(Maybe AttrKey)
  }
  deriving (Show)

instance Eq EL'AttrKey where
  EL'AttrKey _ (Just k1) == EL'AttrKey _ (Just k2) = k1 == k2
  EL'AttrKey (AttrAddrSrc addr1 _) Nothing
    == EL'AttrKey (AttrAddrSrc addr2 _) Nothing = addr1 == addr2
  EL'AttrKey {} == EL'AttrKey {} = False -- or hash/eq laws won't hold

instance Ord EL'AttrKey where
  compare (EL'AttrKey _ (Just k1)) (EL'AttrKey _ (Just k2)) = compare k1 k2
  compare
    (EL'AttrKey (AttrAddrSrc addr1 _) Nothing)
    (EL'AttrKey (AttrAddrSrc addr2 _) Nothing) = compare addr1 addr2
  compare (EL'AttrKey _ Just {}) (EL'AttrKey _ Nothing) = LT
  compare (EL'AttrKey _ Nothing) (EL'AttrKey _ Just {}) = GT

instance Hashable EL'AttrKey where
  hashWithSalt s (EL'AttrKey _ (Just key)) =
    s `hashWithSalt` (1 :: Int) `hashWithSalt` key
  hashWithSalt s (EL'AttrKey (AttrAddrSrc addr _) Nothing) =
    s `hashWithSalt` (2 :: Int) `hashWithSalt` addr

data EL'Value
  = -- | represent values other than a class or an object
    EL'Value
      { el'value'src :: !ExprSrc,
        -- TODO this usefull ??
        el'value'type :: !(Maybe EdhTypeValue),
        -- staticly decidable value, or nil if unable to
        el'value'refied :: !EdhValue
      }
  | -- | a class definition is specially treated in static analysis
    EL'Class
      { el'class'proc :: !ProcDecl,
        -- | scope of this class
        el'class'scope :: !EL'Scope,
        -- | an attribute is exported by any form of assignment targeting
        -- current scope, or any form of procedure declaration, which follows an
        -- `export` keyword, or within a block following an `export` keyword
        el'class'exports :: !EL'Exports
      }
  | -- | an object instance value is specially treated in static analysis
    EL'Object
      { -- | the class of this object instance
        -- TODO use some other, more proper type for this field ?
        el'obj'class :: !EL'OriginalValue,
        -- | the source expression instantiated this object
        el'obj'src :: !ExprSrc
      }

data EL'Section = EL'ScopeSec !EL'Scope | EL'RegionSec !EL'Region

sectionSpan :: EL'Section -> SrcRange
sectionSpan (EL'ScopeSec scope) = el'scope'span scope
sectionSpan (EL'RegionSec region) = el'region'span region

data EL'Scope = EL'Scope
  { el'scope'span :: !SrcRange,
    -- a scope can have nested scopes, and it at least should have a final
    -- region to contain all possible annotations and attributes
    --
    -- a new region is created upon each (group of) attr definition or deletion,
    -- consecutive regions within a scope should be ever expanding in src span
    -- regards
    --
    -- sections within a scope appear naturally in source order, we use an
    -- immutable vector here, so it can be used with binary search to locate
    -- the section for a target location within this scope
    el'scope'sections :: !(Vector EL'Section)
  }

-- | the last section of a scope should always be the full region with all
-- possible attributes
scopeFullRegion :: EL'Scope -> EL'Region
scopeFullRegion (EL'Scope _ !secs) =
  if nSecs < 1
    then error "bug: no section in a scope"
    else case V.unsafeIndex secs (nSecs - 1) of
      EL'RegionSec !region -> region
      _ -> error "bug: last section of a scope not a region"
  where
    !nSecs = V.length secs

-- | a consecutive region covers the src range of its predecessor, with a single
-- add or deletion of an attribute
--
-- note a change of annotation doesn't create a new region
--
-- note the 2 versions of immutable HashMap share as much content as possible in
-- this use case, so they are ideally compact
data EL'Region = EL'Region
  { el'region'span :: !SrcRange,
    -- | an annotation is created by the (::) operator, with left-hand operand
    -- being the attribute key
    el'region'annos :: !(HashMap EL'AttrKey ExprSrc),
    -- | an attribute is created by any form of assignment targeting current
    -- scope, or any form of procedure declaration
    el'region'attrs :: !(HashMap EL'AttrKey EL'OriginalValue),
    -- | an effectiful attribute is created by any form of assignment targeting
    -- current scope, or any form of procedure declaration, which follows an
    -- `effect` keyword, or within a block following an `effect` keyword
    el'region'effs :: !(HashMap EL'AttrKey EL'OriginalValue)
  }
