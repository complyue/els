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
    -- a new region is created upon each attr definition or deletion
    --
    -- sections within a scope appear naturally in source order, so this vector
    -- can be used with binary search for a target location within this scope
    el'scope'sections :: !(Vector EL'Section)
  }

-- | the last region should be the full region with all possible attrs
scopeFullRegion :: EL'Scope -> EL'Region
scopeFullRegion (EL'Scope _ !secs) = go $ V.length secs - 1
  where
    go :: Int -> EL'Region
    go !i | i < 0 = error "bug: no region in a scope?!"
    go i = case V.unsafeIndex secs i of
      EL'RegionSec !region -> region
      _ -> go $ i -1

-- | a consecutive region covers the src range of its predecessor, with a single
-- add or deletion of an attribute
--
-- note a change of annotation doesn't create a new region
--
-- note the 2 versions of immutable HashMap share as much content as possible in
-- this use case, so is ideally compact
data EL'Region = EL'Region
  { el'region'span :: !SrcRange,
    -- | an annotation is created by the (::) operator, with left-hand operand
    -- being the attribute key
    el'region'annos :: !(HashMap AttrKey EL'Value),
    -- | an attribute is created by any form of assignment, targeting the
    -- current scope
    el'region'attrs :: !(HashMap AttrKey EL'Value)
  }

data EL'Value = EL'Value
  { el'value'src :: !ExprSrc,
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
    -- | exported artifacts, the order is preserved as artifacts get exported
    el'modu'exports :: !EL'Exports
  }

type EL'Exports = OrderedDict AttrKey EL'Value

data EL'Home = EL'Home
  { -- | each parent dir of `edh_modules` is considered an Edh home
    el'home'path :: !Text,
    -- | loaded modules under this home
    -- module name is path (with `.edh` and `/__init__.edh` stripped off), and
    -- relative to the `edh_modules` dir
    el'home'modules :: !(TMVar (Map.HashMap ModuleName EL'Module))
  }

type ModuleName = Text
