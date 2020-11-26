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
import Prelude

data EL'Home = EL'Home
  { -- | each parent dir of `edh_modules` is considered an Edh home
    --
    -- an Edh home's path should always be absolute and as canonical as possible
    el'home'path :: !Text,
    -- | usual modules under this home
    --
    -- a usual module is importable with absolute module path, its src file must
    -- reside inside the `edh_modules` subdir under an Edh home root dir, and
    -- the file name usually does not start with an underscore char (e.g.
    -- `__main__.edh` is an entry module and not importable). one exceptional
    -- case that e.g. is
    -- `$edh_home/edh_modules/some/modu/__init__.edh` will assume module path
    -- `some/modu` thus importable with it, it will conflict with
    -- `$edh_home/edh_modules/some/modu.edh` if both exist.
    --
    -- the name of a usual module is path with `.edh` and `/__init__.edh`
    -- stripped off, and relative to the `edh_modules` dir.
    --
    -- note all Edh src file should have the extension name `.edh`, and will be
    -- stripped off from any Edh module name or module path.
    el'home'modules :: !(TMVar (Map.HashMap ModuleName EL'ModuSlot)),
    -- | standalone script modules under this home
    --
    -- a script module is technically a standalone module, only importable with
    -- relative path but seldom get imported in practice, it usually run as an
    -- entry module.
    --
    -- typical script modules reside outside of the `edh_modules` subdir, one
    -- speciall case is `__main__.edh` e.g.
    -- `$edh_home/edh_modules/some/modu/__main__.edh` will be executed when
    -- `some/modu` is specified as the target module per Edh interpreter run.
    --
    -- the advantage of using a usual module path as target, over a script
    -- module per running is, so that you can address installed modules without
    -- knowning where exactly it is located, while a nested Edh home can have a
    -- local module file overriding one from outer homes.
    --
    -- the name of a script module is path relative to the home root dir, with
    -- `.edh` extension preserved, but with the exception of a `__main__.edh`
    -- module script, whose script name is the same as the module path of its
    -- parent dir.
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
    -- | the relative base path for this module, relative import will cause
    -- error if this is set to empty
    el'modu'rel'base :: !Text,
    -- TODO add fields corresponding to `__name__` `__path__` in the rt module

    -- | absolute path of the `.edh` src file
    -- this corresponds to `__file__` in the module at runtime
    el'modu'doc :: !SrcDoc,
    -- fields pertain results from different stages of analysation
    -- the 1st layer of `TMVar` when non-empty means it has been worked on,
    -- the 2nd layer of the `TMVar` provides awaitable result from the WIP, and
    -- if non-empty, means the work has already been done.
    -- clearing the 1st layer `TMVar` invalidates previous analysis work, `while
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
    el'loaded'arts :: !EL'Artifacts,
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
    -- el'modu'imports :: !EL'Artifacts,
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

el'AttrKey :: AttrAddrSrc -> EL'AttrKey
el'AttrKey asrc@(AttrAddrSrc !addr _) = case addr of
  NamedAttr !strName -> EL'AttrKey asrc $ Just $ AttrByName strName
  QuaintAttr !strName -> EL'AttrKey asrc $ Just $ AttrByName strName
  SymbolicAttr {} -> EL'AttrKey asrc Nothing

data EL'ArgsPack = EL'ArgsPack ![EL'Value] !(OrderedDict EL'AttrKey EL'Value)

data EL'Value
  = -- | runtime constant i.e. decidable at analysis time
    EL'Const !EdhValue
  | -- | apk not fully decidable at analysis time
    EL'Apk !EL'ArgsPack
  | -- | runtime value whose reification can not be decided at analysis time
    EL'Value
      { -- | the original module defined this value
        el'origin'module :: !EL'ModuSlot,
        -- | TODO will this be useful ?
        -- el'origin'eff'span :: !SrcRange,
        -- | the src expression creating this value
        el'value'src :: !ExprSrc,
        -- | staged result however this value is decided
        el'value'stage :: !(TVar EL'ValStage),
        -- type if possibly decidable at analysis time
        el'value'type :: !(Maybe EdhTypeValue)
      }

data EL'ValStage
  = EL'ParsedValue
  | EL'AnnotatedValue !EL'Value
  | EL'LoadedClass
      { el'class'loaded'name :: EL'AttrKey,
        -- | supers
        el'class'loaded'supers :: ![EL'Value],
        -- | member artifacts
        el'class'loaded'arts :: !EL'Artifacts,
        -- | member artifacts
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
