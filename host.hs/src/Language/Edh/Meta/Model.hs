module Language.Edh.Meta.Model where

-- import           Debug.Trace

import Control.Concurrent.STM
import Control.Monad
import Control.Monad.ST
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as Map
import Data.Hashable
import Data.Text (Text)
import qualified Data.Text as T
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV
import Language.Edh.EHI
import Language.Edh.RtTypes
import Prelude

data EL'Section = EL'ScopeSec !EL'Scope | EL'RegionSec !EL'Region

sectionSpan :: EL'Section -> SrcRange
sectionSpan (EL'ScopeSec scope) = el'scope'span scope
sectionSpan (EL'RegionSec region) = el'region'span region

data EL'Scope = EL'Scope
  { el'scope'span :: !SrcRange,
    -- a scope can have nested scopes, and it at least should have a final
    -- region to contain all possible annotations and attributes
    --
    -- a new region is created upon each attr definition or deletion,
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
    el'region'annos :: !(HashMap AttrKey ExprSrc),
    -- | an attribute is created by any form of assignment targeting current
    -- scope, or any form of procedure declaration
    el'region'attrs :: !(HashMap AttrKey EL'Value),
    -- | an effectiful attribute is created by any form of assignment targeting
    -- current scope, or any form of procedure declaration, which follows an
    -- `effect` keyword, or within a block following an `effect` keyword
    el'region'effs :: !(HashMap AttrKey EL'Value)
  }

data EL'Class = EL'Class
  { el'class'scope :: !EL'Scope,
    -- | an attribute is exported by any form of assignment targeting
    -- current scope, or any form of procedure declaration, which follows an
    -- `export` keyword, or within a block following an `export` keyword
    el'class'exports :: !EL'Exports
  }

-- | the dict of artifacts by attribute key, for those exported from an object
-- (a module object or vanilla object), with their order of export preserved
type EL'Exports = OrderedDict AttrKey EL'Value

-- | an Edh language level value is created by any form of assignment targeting
-- current scope, or any form of procedure declaration
data EL'Value = EL'Value
  { el'value'span :: !SrcRange,
    el'value'src :: !ExprSrc,
    el'value'refied :: !(TVar EdhValue)
  }

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

data EL'Home = EL'Home
  { -- | each parent dir of `edh_modules` is considered an Edh home
    el'home'path :: !Text,
    -- | loaded modules under this home
    -- module name is path (with `.edh` and `/__init__.edh` stripped off), and
    -- relative to the `edh_modules` dir
    el'home'modules :: !(TMVar (Map.HashMap ModuleName EL'Module))
  }

type ModuleName = Text
