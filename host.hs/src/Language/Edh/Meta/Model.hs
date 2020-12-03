module Language.Edh.Meta.Model where

-- import           Debug.Trace

import Control.Concurrent.STM
import Data.HashMap.Strict (HashMap)
import Data.Hashable
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Language.Edh.EHI
import Prelude

-- diagnostic data structures per LSP specification 3.15

el'LogDiag ::
  TVar [EL'Diagnostic] ->
  EL'DiagSeverity ->
  SrcRange ->
  Text ->
  Text ->
  STM ()
el'LogDiag !diags !severity !src'span !code !msg =
  modifyTVar' diags (el'Diag severity src'span code msg :)

el'Diag :: EL'DiagSeverity -> SrcRange -> Text -> Text -> EL'Diagnostic
el'Diag !severity !src'span !code !msg =
  EL'Diagnostic
    { el'diag'range = src'span,
      el'diag'severity = severity,
      el'diag'code = Right code,
      el'diag'source = "els",
      el'diag'message = msg,
      el'diag'tags = []
    }

data EL'Diagnostic = EL'Diagnostic
  { el'diag'range :: !SrcRange,
    el'diag'severity :: !EL'DiagSeverity,
    el'diag'code :: !(Either Int Text),
    el'diag'source :: !Text,
    el'diag'message :: !Text,
    el'diag'tags :: ![EL'DiagnosticTag]
  }

type EL'DiagSeverity = Int

el'Error, el'Warning, el'Information, el'Hint :: EL'DiagSeverity
el'Error = 1
el'Warning = 2
el'Information = 3
el'Hint = 4

type EL'DiagnosticTag = Int

el'Unnecessary, el'Deprecated :: EL'DiagnosticTag
el'Unnecessary = 1
el'Deprecated = 2

-- Edh module files are organized into a hierarchy of Edh homes, they can import
-- eachothers, where cyclic imports are allowed, but each module is evaluated
-- synchronously by default, so ultimately exported artifacts may not be
-- available immediately after the `import` expression introducing them into
-- current module.
--
-- Special treatments is needed in case an import can not finish synchronously
-- during the analysation, `TMVar`s are generally used to place a slot for
-- the result that can only be obtained after the importee has actually made
-- the respective export available.

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
    el'home'modules :: !(TMVar (HashMap ModuleName EL'ModuSlot)),
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
    el'home'scripts :: !(TMVar (HashMap ScriptName EL'ModuSlot))
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
    -- | tracking the parsing of this module
    el'modu'parsing :: !(TMVar EL'ModuParsing),
    -- | tracking the resolving of this module
    el'modu'resolution :: !(TMVar EL'ModuResolution)
  }

instance Eq EL'ModuSlot where
  x == y = el'modu'doc x == el'modu'doc y

instance Hashable EL'ModuSlot where
  hashWithSalt s v =
    let SrcDoc !absPath = el'modu'doc v
     in hashWithSalt s absPath

data EL'ModuParsing
  = EL'ModuParsing !(TVar [EL'ParsedModule -> STM ()])
  | EL'ModuParsed !EL'ParsedModule

data EL'ParsedModule = EL'ParsedModule
  { el'modu'doc'comment :: !(Maybe DocComment),
    el'modu'stmts :: ![StmtSrc],
    -- | diagnostics generated from this stage of analysis
    el'parsing'diags :: ![EL'Diagnostic]
  }

data EL'ModuResolution
  = EL'ModuResolving !(TVar [EL'ResolvedModule -> STM ()])
  | EL'ModuResolved !EL'ResolvedModule

data EL'ResolvedModule = EL'ResolvedModule
  { -- | there will be nested scopes appearing in natural source order, within
    -- this root scope of the module
    el'resolved'scope :: !EL'Scope,
    -- | exports from this module, mutated upon any origin module of re-exports
    -- get resolved
    el'resolved'exports :: !EL'Exports,
    -- | other modules those should be invalidated once this module is changed
    --
    -- note a dependant may stop depending on this module due to src changes,
    -- so cross checking of its `el'resolved'dependencies` should be performed and
    -- have this `el'resolved'dependants` updated upon such changes
    el'resolved'dependants :: !(TVar (HashMap EL'ModuSlot Bool)),
    -- | other modules this module depends on
    --
    -- a dependency module's `el'resolved'dependants` should be updated marking
    -- this module as a dependant as well
    --
    -- note after invalidated, re-analysation of this module may install a new
    -- version of this map reflecting dependencies up-to-date
    el'resolved'dependencies :: !(TVar (HashMap EL'ModuSlot Bool)),
    -- | diagnostics generated from this stage of analysis
    el'resolution'diags :: ![EL'Diagnostic]
  }

-- All attributes are local to a context module, with respects to both defining
-- & referencing. In case of importing, the import expression should serve the
-- attribute definition, with the origin and possible renames tracked.

type EL'Exports = IOPD AttrKey EL'AttrDef

-- | an attribute definition or re-definition (i.e. update to a previously
-- defined attribute)
--
-- technically (re)defining an attribute is the same as binding a (mutable or
-- immutable) value to an attribute key per the backing entity of some scope
data EL'AttrDef = EL'AttrDef
  { -- | the key of this attribute
    el'attr'def'key :: !AttrKey,
    -- | doc comment preceeding this definition
    el'attr'doc'cmt :: !DocComment,
    -- | the origin of this definition, typically for attributes imported from
    -- other modules, the original module and export key is represented here
    el'attr'def'origin :: !(Maybe (EL'ModuSlot, AttrKey)),
    -- | the operation created this attribute
    -- in addition to assignment operators e.g. @=@ @+=@ etc. it can be
    -- @<arrow>@, @<proc-def>@, @<import>@ and @<let>@ etc.
    el'attr'def'op :: !OpSymbol,
    -- | the source span to highlight when this definition is located
    el'attr'def'focus :: !SrcRange,
    -- | the full expression created this attribute
    el'attr'def'expr :: !ExprSrc,
    -- | the attribute value, can only be filled after fully resolved
    el'attr'def'value :: !(TMVar EL'Value),
    -- | annotation to this attribute
    --
    -- note multiple definitions to a same attribute key can have separate
    -- annotations
    el'attr'def'anno :: !(Maybe EL'AttrAnno),
    -- | previous definition, in case this definition is an update to an
    -- previously existing attribute
    el'attr'prev'def :: !(Maybe EL'AttrDef)
  }

-- | an annotation created by the (::) operator
data EL'AttrAnno = EL'AttrAnno
  { -- | right-hand expression to the (::) operator
    el'anno'expr :: !ExprSrc,
    -- | source text of the annotation, this can show up on IDE hover, at least
    -- before we can generate more sophisticated descriptions for that
    el'anno'text :: !Text,
    -- | resolved value of the right-hand expression
    --
    -- TODO this doesn't seem guaranteed to be resolvable to some value, maybe
    --      here we need some dedicated data structure for representation of
    --      various annotations, wrt how they are interpreted - mostly for
    --      type hints, maybe even more other semantics?
    el'anno'value :: !(TMVar EL'Value)
  }

-- | an attribute reference, links to its respective definition
data EL'AttrRef = EL'AttrRef
  { -- | local key used to refer to this attribute
    el'attr'ref'key :: !AttrKey,
    -- | the definition introduced this attribute
    -- this field is guaranteed to be filled only after all outer scopes have
    -- been loaded
    el'attr'ref'def :: !EL'AttrDef
  }

data EL'ArgsPack = EL'ArgsPack ![EL'Value] !(OrderedDict AttrKey EL'Value)

data EL'Value
  = -- | runtime constant i.e. decidable at analysis time
    EL'Const !EdhValue
  | -- | apk at analysis time
    -- TODO should an apk with every element decidable to be an `EL'Const` ?
    EL'Apk !EL'ArgsPack
  | -- | an arbitrary expression not resolved at analysis time
    EL'Expr !ExprSrc
  | -- | a module object
    EL'ModuVal !EL'ModuSlot
  | -- | a procedure
    EL'ProcVal !EL'Proc
  | -- | an object
    EL'ObjVal !EL'Object
  | -- | a class
    EL'ClsVal !EL'Class

-- | a procedure
data EL'Proc = EL'Proc
  { el'proc'name :: AttrKey,
    -- | scope of this proc
    el'proc'scope :: !EL'Scope
  }

-- | an object, with module and namespace being special cases
data EL'Object = EL'Object
  { el'obj'class :: !EL'Class,
    -- the `supers` list of an object at runtime is instances created
    -- according to its class' `mro` list, plus more super objects appended
    -- by `extends` statements (usually from within the `__init__()` method
    -- but dynamic `extends` from arbitrary methods whenever called is also
    -- allowed)
    --
    -- this list is collected at analysis time
    el'obj'exts :: ![EL'Object],
    -- | object attributes are exported from the object initialising
    -- procedure in case of a module or namespace object, and typically
    -- from the `__init__()` method otherwise. while it is allowed to
    -- export artifacts from an arbitrary instance method whenever called,
    -- which should probably be considered unusual.
    el'obj'exps :: !EL'Exports
  }

-- | a class
data EL'Class = EL'Class
  { el'class'name :: AttrKey,
    -- | extends
    el'class'exts :: ![EL'Class],
    -- | C3 linearized mro list
    el'class'mro :: ![EL'Class],
    -- | scope of the class initializing procedure
    el'class'scope :: !EL'Scope,
    -- | class attributes are exported from the class defining procedure, while
    -- it is allowed to export artifacts from an arbitrary class method whenever
    -- called, which should probably be considered unusual.
    el'class'exps :: !EL'Exports
  }

data EL'Section = EL'ScopeSec !EL'Scope | EL'RegionSec !EL'Region

sectionSpan :: EL'Section -> SrcRange
sectionSpan (EL'ScopeSec scope) = el'scope'span scope
sectionSpan (EL'RegionSec region) = el'region'span region

-- | a scope is backed by an entity with arbitrary attributes, as Edh allows
-- very straight forward sharing of lexical scopes to goroutines spawned from
-- within an inner scope, it may be more right to assume all attributes ever
-- defined in outer scopes are accessible, before we can represent sequential
-- order of attribute availablility with respect to precise concurrency analysis
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
    el'scope'sections :: !(Vector EL'Section),
    -- | the 1st appearances of each attribute defined in this scope
    el'scope'attrs :: !(OrderedDict AttrKey EL'AttrDef),
    -- | the 1st appearances of each effectful attribute defined in this scope
    el'scope'effs :: !(OrderedDict AttrKey EL'AttrDef),
    -- | all symbols encountered in this scope, in order as appeared in src
    el'scope'symbols :: !(Vector EL'AttrSym)
  }

-- | a symbol at source level is, an attribute definitions or attribute
-- reference, the order of symbols in this vector reflects the order each
-- symbol appears in src code reading order
data EL'AttrSym = EL'DefSym !EL'AttrDef | EL'RefSym !EL'AttrRef

-- | the last section of a scope should always be the full region with all
-- possible attributes
scopeFullRegion :: EL'Scope -> EL'Region
scopeFullRegion !scope =
  if nSecs < 1
    then error "bug: no section in a scope"
    else case V.unsafeIndex secs (nSecs - 1) of
      EL'RegionSec !region -> region
      _ -> error "bug: last section of a scope not a region"
  where
    !secs = el'scope'sections scope
    !nSecs = V.length secs

-- | a consecutive region covers the src range of its predecessor, with a single
-- addition or deletion of an attribute definition
--
-- note a re-definition or a change of annotation doesn't create a new region
data EL'Region = EL'Region
  { el'region'span :: !SrcRange,
    -- | available attributes defined in this region
    el'region'attrs :: !(OrderedDict AttrKey EL'AttrDef)
  }
