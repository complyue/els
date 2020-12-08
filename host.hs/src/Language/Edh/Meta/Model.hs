module Language.Edh.Meta.Model where

-- import           Debug.Trace

import Control.Concurrent.STM
import Data.HashMap.Strict (HashMap)
import Data.Hashable
import Data.Text (Text)
import qualified Data.Text as T
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.IO (unsafePerformIO)
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

instance Show EL'ModuSlot where
  show !ms =
    let (SrcDoc !file) = el'modu'doc ms
     in "<modu-slot: " <> T.unpack file <> ">"

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
    el'resolved'exports :: !EL'ArtsWIP,
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

type EL'ArtsWIP = IOPD AttrKey EL'AttrDef

instance Show EL'ArtsWIP where
  show _exps = "<artifacts>"

-- | an attribute definition or re-definition (i.e. update to a previously
-- defined attribute)
--
-- technically (re)defining an attribute is the same as binding a (mutable or
-- immutable) value to an attribute key per the backing entity of some scope
data EL'AttrDef = EL'AttrDef
  { -- | the key of this attribute
    el'attr'def'key :: !AttrKey,
    -- | doc comment preceeding this definition
    el'attr'doc'cmt :: !(Maybe DocComment),
    -- | the operation created this attribute
    -- in addition to assignment operators e.g. @=@ @+=@ etc. it can be
    -- @<arrow>@, @<proc-def>@, @<import>@ and @<let>@ etc.
    el'attr'def'op :: !OpSymbol,
    -- | the source span to highlight when this definition is located
    el'attr'def'focus :: !SrcRange,
    -- | the full expression created this attribute
    el'attr'def'expr :: !ExprSrc,
    -- | the attribute value, can only be filled after fully resolved
    el'attr'def'value :: !EL'Value,
    -- | annotation to this attribute
    --
    -- note multiple definitions to a same attribute key can have separate
    -- annotations
    el'attr'def'anno :: !(TVar (Maybe EL'AttrAnno)),
    -- | previous definition, in case this definition is an update to an
    -- previously existing attribute
    el'attr'prev'def :: !(Maybe EL'AttrDef)
  }

instance Show EL'AttrDef where
  show !adef =
    "<attr-def: " <> T.unpack (attrKeyStr $ el'attr'def'key adef) <> ">"

el'UltimateValue :: EL'AttrDef -> EL'Value
el'UltimateValue !def = case el'attr'def'value def of
  EL'External _ms !def' -> el'UltimateValue def'
  !val -> val

-- | an annotation created by the (::) operator
data EL'AttrAnno = EL'AttrAnno
  { -- | right-hand expression to the (::) operator
    el'anno'expr :: !ExprSrc,
    -- | doc comment of the annotation
    -- this can show up on IDE hover, at least before we can generate more
    -- sophisticated descriptions for that
    el'anno'doc :: !(Maybe DocComment)
  }

-- | 冇 annotation
maoAnnotation :: TVar (Maybe a)
maoAnnotation = unsafePerformIO $ newTVarIO Nothing
{-# NOINLINE maoAnnotation #-}

-- | an attribute reference, links to its respective definition
data EL'AttrRef = EL'AttrRef
  { -- | the referencing addressor
    el'attr'ref'addr :: !AttrAddrSrc,
    -- | the definition introduced this attribute
    -- this field is guaranteed to be filled only after all outer scopes have
    -- been loaded
    el'attr'ref'def :: !EL'AttrDef
  }

instance Show EL'AttrRef where
  show (EL'AttrRef (AttrAddrSrc !addr _span) _adef) =
    "<ref: " <> show addr <> ">"

data EL'ArgsPack = EL'ArgsPack ![EL'Value] !(OrderedDict AttrKey EL'Value)

instance Show EL'ArgsPack where
  show (EL'ArgsPack !args !kwargs) =
    if null args && odNull kwargs
      then "()"
      else "( " <> pos args <> kw (odToList kwargs) <> ")"
    where
      pos [] = ""
      pos (a : rest) = show a <> ", " <> pos rest
      kw [] = ""
      kw ((k, a) : rest) = show k <> "= " <> show a <> ", " <> kw rest

data EL'Value
  = -- | runtime constant i.e. decidable at analysis time
    EL'Const !EdhValue
  | -- | externally defined value, most probably imported
    EL'External !EL'ModuSlot !EL'AttrDef
  | -- | apk at analysis time
    EL'Apk !EL'ArgsPack
  | -- | list at analysis time
    EL'List !(TVar [EL'Value])
  | -- | dict at analyze time
    EL'Dict !(TVar [(EL'Value, EL'Value)])
  | -- | an object
    EL'ObjVal !EL'Object
  | -- | a class
    EL'ClsVal !EL'Class
  | -- | a module object
    EL'ModuVal !EL'ModuSlot
  | -- | a procedure
    EL'ProcVal !EL'Proc
  | -- | a property
    EL'PropVal !EL'Class !AttrKey
  | -- | an arbitrary expression not resolved at analysis time
    EL'Expr !ExprSrc

instance Show EL'Value where
  show (EL'Const !x) = show x
  show (EL'External !ms !adef) =
    let !k = el'attr'def'key adef
        (SrcDoc !file) = el'modu'doc ms
     in "<ref: " <> show k <> " from " <> T.unpack file <> ">"
  show (EL'Apk !apk) = show apk
  show (EL'List _lv) = "<list>" -- TODO avoid TVar then showable here?
  show (EL'Dict _dv) = "<dict>" -- TODO avoid TVar then showable here?
  show (EL'ObjVal !obj) = show obj
  show (EL'ClsVal !cls) = show cls
  show (EL'ModuVal !modu) = show modu
  show (EL'ProcVal !p) = show p
  show (EL'PropVal !cls !prop) = show cls <> "." <> show prop
  show (EL'Expr !x) = show x

-- | a procedure
data EL'Proc = EL'Proc
  { el'proc'name :: AttrKey,
    el'proc'args :: !ArgsReceiver,
    -- | scope of this proc
    el'proc'scope :: !EL'Scope
  }
  deriving (Show)

-- | an object, with module and namespace being special cases
data EL'Object
  = EL'ClsObj !EL'Class
  | EL'Object
      { el'obj'class :: !EL'Class,
        -- | the `supers` list of an object at runtime is instances created
        -- according to its class' `mro` list, plus more super objects appended
        -- by `extends` statements (usually from within the `__init__()` method
        -- but dynamic `extends` from arbitrary methods whenever called is also
        -- allowed)
        --
        -- this list is collected at analysis time
        el'obj'exts :: ![EL'Object],
        -- | all attributes of the object
        el'obj'attrs :: !EL'Artifacts,
        -- | object attributes are exported from the object initialising
        -- procedure in case of a module or namespace object, and typically
        -- from the `__init__()` method otherwise. while it is allowed to
        -- export artifacts from an arbitrary instance method whenever called,
        -- which should probably be considered unusual.
        el'obj'exps :: !EL'Artifacts
      }
  deriving (Show)

-- | a class
data EL'Class = EL'Class
  { el'class'name :: AttrKey,
    -- | extends
    el'class'exts :: ![EL'Object],
    -- | C3 linearized mro list
    el'class'mro :: ![EL'Class],
    -- | scope of the class initializing procedure
    el'class'scope :: !EL'Scope,
    -- | class attributes are exported from the class defining procedure, while
    -- it is allowed to export artifacts from an arbitrary class method whenever
    -- called, which should probably be considered unusual.
    el'class'exps :: !EL'Artifacts
  }
  deriving (Show)

el'MetaClass :: EL'Class
el'MetaClass =
  EL'Class
    (AttrByName "class")
    []
    []
    ( EL'Scope
        noSrcRange
        V.empty
        V.empty
        ( odFromList
            [ ( AttrByName "name",
                EL'AttrDef
                  (AttrByName "name")
                  Nothing
                  "<class-intrinsic>"
                  noSrcRange
                  (ExprSrc (LitExpr NilLiteral) noSrcRange)
                  (EL'PropVal el'MetaClass (AttrByName "name"))
                  maoAnnotation
                  Nothing
              )
            ]
        )
        odEmpty
        V.empty
    )
    odEmpty
{-# NOINLINE el'MetaClass #-}

el'NamespaceClass :: EL'Class
el'NamespaceClass =
  EL'Class (AttrByName "<namespace>") [] [] maoScope odEmpty
{-# NOINLINE el'NamespaceClass #-}

el'ModuleClass :: EL'Class
el'ModuleClass =
  EL'Class (AttrByName "<module>") [] [] maoScope odEmpty
{-# NOINLINE el'ModuleClass #-}

el'ScopeClass :: EL'Class
el'ScopeClass =
  EL'Class (AttrByName "<scope>") [] [] maoScope odEmpty
{-# NOINLINE el'ScopeClass #-}

-- | a scope is backed by an entity with arbitrary attributes, as Edh allows
-- very straight forward sharing of lexical scopes to goroutines spawned from
-- within an inner scope, it may be more right to assume all attributes ever
-- defined in outer scopes are accessible, before we can represent sequential
-- order of attribute availablility with respect to precise concurrency analysis
data EL'Scope = EL'Scope
  { el'scope'span :: !SrcRange,
    -- | nested scopes
    el'scope'inner'scopes :: !(Vector EL'Scope),
    -- | a new region is created upon each (group of) attr definition or
    -- deletion
    --
    -- sections within a scope appear naturally in source order, we use an
    -- immutable vector here, so it can be used with binary search to locate
    -- the region for a target location within this scope
    el'scope'regions :: !(Vector EL'Region),
    -- | the 1st appearances of each attribute defined in this scope
    el'scope'attrs :: !EL'Artifacts,
    -- | the 1st appearances of each effectful attribute defined in this scope
    el'scope'effs :: !EL'Artifacts,
    -- | all symbols encountered in this scope, in order as appeared in src
    el'scope'symbols :: !(Vector EL'AttrSym)
  }
  deriving (Show)

-- | 冇 scope
maoScope :: EL'Scope
maoScope = EL'Scope noSrcRange V.empty V.empty odEmpty odEmpty V.empty

-- | a consecutive region covers the src range of its predecessor, with a single
-- addition or deletion of an attribute definition
--
-- note a re-definition or a change of annotation doesn't create a new region
data EL'Region = EL'Region
  { el'region'begin :: !SrcPos,
    -- | available attributes defined in this region
    el'region'attrs :: !EL'Artifacts
  }
  deriving (Show)

type EL'Artifacts = OrderedDict AttrKey EL'AttrDef

instance Show EL'Artifacts where
  show _arts = "<artifacts>"

-- | a symbol at source level is, an attribute definitions or attribute
-- reference, the order of symbols in this vector reflects the order each
-- symbol appears in src code reading order
data EL'AttrSym = EL'DefSym !EL'AttrDef | EL'RefSym !EL'AttrRef
  deriving (Show)
