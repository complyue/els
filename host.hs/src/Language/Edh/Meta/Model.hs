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
    -- | importable modules under this home
    --
    -- a module is importable iif the src file resides inside the `edh_modules`
    -- subdir under an Edh home root dir, and the file name does not start with
    -- an underscore char (e.g. named `__main__.edh`), one special case that
    -- e.g.
    -- `$edh_home/edh_modules/some/modu/__init__.edh` will shadow
    -- `$edh_home/edh_modules/some/modu.edh`, assuming the name `some/modu`.
    --
    -- the name of an importable module is path (with `.edh` and `/__init__.edh`
    -- stripped off), and relative to the `edh_modules` dir.
    --
    -- note all Edh src file should have the extension name `.edh`, and will be
    -- stripped off from any Edh module name or module path.
    el'home'modules :: !(TMVar (Map.HashMap ModuleName EL'ModuSlot)),
    -- | standalone scripts under this home
    --
    -- a script is technically a standalone module that not importable, it can
    -- only be run as an entry module.
    --
    -- typical script files reside outside of the `edh_modules` sub dir, one
    -- speciall case is `__main__.edh` e.g.
    -- `$edh_home/edh_modules/some/modu/__main__.edh` will be executed when
    -- `some/modu` is specified as the target module per Edh interpreter run.
    --
    -- the advantage of a module target over a file target per running is that
    -- module resolution machinery is more flexible so you can address installed
    -- modules while a nested Edh home can have a local file overriding it.
    --
    -- the name of a script is path relative to the home root dir, with `.edh`
    -- extension name preserved, but with the exception of a module script,
    -- whose script name is the same as its module name.
    el'home'scripts :: !(TMVar (Map.HashMap ScriptName EL'ModuSlot))
    -- todo cache configurations per Edh home with more fields
  }

type ModuleName = Text

type ScriptName = Text

instance Eq EL'Home where
  x == y = el'home'path x == el'home'path y

-- | Edh module and `.edh` text doc (os file, virtual or physical, local or
-- remote) be of 1:1 mapping
data EL'ModuSlot = EL'ModuSlot
  { -- | each parent dir of `edh_modules` is considered an Edh home
    el'modu'home :: !EL'Home,
    -- | absolute path of the `.edh` src file
    el'modu'doc :: !SrcDoc,
    -- fields pertain results from different stages of analysation
    -- the 1st layer of `TMVar` when non-empty means it has been worked on,
    -- the 2nd layer of the `TMVar` provides awaitable result from the WIP, and
    -- if non-empty, means the work has already been done.
    -- clearing the 1st layer `TMVar` invalidates previous analysis work, while
    -- the 2nd layer `TMVar` should usually not be cleared once filled.
    el'modu'parsed :: !(TMVar (TMVar EL'ParsedModule)),
    el'modu'loaded :: !(TMVar (TMVar EL'LoadedModule)),
    el'modu'resolved :: !(TMVar (TMVar EL'ResolvedModule)),
    -- | other modules those should be invalidated once this module is changed
    --
    -- note a dependant may stop depending on this module due to src changes,
    -- so cross checking of its `el'modu'dependencies` should be performed and
    -- have this `el'modu'dependants` updated upon such changes
    el'modu'dependants :: !(TVar (Map.HashMap EL'ModuSlot Bool)),
    -- | other modules this module depends on
    --
    -- a dependency module's `el'modu'dependants` should be updated marking
    -- this module as a dependant as well
    --
    -- note after invalidated, re-analysation of this module may install a new
    -- version of this map reflecting dependencies up-to-date
    el'modu'dependencies :: !(TVar (Map.HashMap EL'ModuSlot Bool))
  }

instance Eq EL'ModuSlot where
  x == y = el'modu'doc x == el'modu'doc y

instance Hashable EL'ModuSlot where
  hashWithSalt s v =
    let SrcDoc !absPath = el'modu'doc v
     in hashWithSalt s absPath

data EL'ParsedModule = EL'ParsedModule
  { el'parsed'stmts :: ![StmtSrc],
    -- | diagnostics generated from this stage of analysis
    el'parsed'diags :: ![(SrcRange, Text)]
  }

data EL'LoadedModule = EL'LoadedModule
  { -- | artifacts identified before resolution
    el'loaded'arts :: OrderedDict EL'AttrKey EL'Value,
    -- | exports identified before resolution
    el'loaded'exports :: !EL'Artifacts,
    -- | diagnostics generated from this stage of analysis
    el'loaded'diags :: ![(SrcRange, Text)]
  }

data EL'ResolvedModule = EL'ResolvedModule
  { -- | there will be nested scopes appearing in natural source order, within
    -- this root scope of the module
    el'resolved'scope :: !EL'Scope,
    -- | TODO this useful?
    -- el'modu'imports :: OrderedDict EL'AttrKey EL'Value,
    -- | an attribute is exported by any form of assignment targeting
    -- current scope, or any form of procedure declaration, which follows an
    -- `export` keyword, or within a block following an `export` keyword
    el'resolved'exports :: !EL'Artifacts,
    -- | diagnostics generated from this stage of analysis
    el'resolved'diags :: ![(SrcRange, Text)]
  }

-- | a dict of artifacts by attribute key, with their order of appearance
-- preserved
type EL'Artifacts = OrderedDict EL'AttrKey EL'Value

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
  = -- | runtime constant i.e. decidable at analysis time
    EL'RtConst !EdhValue
  | -- | runtime value whose reification can not be decided at analysis time
    EL'RtValue
      { -- | the original module defined this value
        el'origin'module :: !EL'ModuSlot,
        -- | TODO will this be useful ?
        -- el'origin'eff'span :: !SrcRange,
        -- | the src expression creating this value
        el'value'src :: !ExprSrc,
        -- | staged result however this value is decided
        el'value'stage :: !(TVar EL'ValStage),
        -- annotated type of this value, most likely from annotations
        el'value'type :: !(Maybe EL'Value)
      }

data EL'ValStage
  = EL'ParsedValue
  | EL'LoadedClass
      { el'class'loaded'name :: EL'AttrKey,
        -- | mro
        el'class'loaded'mro :: ![EL'Value],
        -- | an attribute is exported by any form of assignment targeting
        -- current scope, or any form of procedure declaration, which follows an
        -- `export` keyword, or within a block following an `export` keyword
        el'class'loaded'exports :: !EL'Artifacts
      }
  | EL'ResolvedClass
      { el'class'resolved'name :: EL'AttrKey,
        -- | mro
        el'class'resolved'mro :: ![EL'Value],
        -- | scope of this class
        el'class'resolved'scope :: !EL'Scope,
        -- | an attribute is exported by any form of assignment targeting
        -- current scope, or any form of procedure declaration, which follows an
        -- `export` keyword, or within a block following an `export` keyword
        el'class'resolved'exports :: !EL'Artifacts
      }
  | EL'LoadedObject
      { -- | the class of this object instance
        -- TODO use some other, more proper type for this field ?
        el'obj'loaded'class :: !EL'Value,
        -- | loaded super instances
        el'obj'loaded'supers :: ![EL'Value]
      }
  | EL'ResolvedObject
      { -- | the class of this object instance
        -- TODO use some other, more proper type for this field ?
        el'obj'resolved'class :: !EL'Value,
        -- | resolved super instances
        el'obj'resolved'supers :: ![EL'Value]
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
    el'region'attrs :: !(HashMap EL'AttrKey EL'Value),
    -- | an effectiful attribute is created by any form of assignment targeting
    -- current scope, or any form of procedure declaration, which follows an
    -- `effect` keyword, or within a block following an `effect` keyword
    el'region'effs :: !(HashMap EL'AttrKey EL'Value)
  }
