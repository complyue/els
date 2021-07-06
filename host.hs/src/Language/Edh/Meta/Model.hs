module Language.Edh.Meta.Model where

-- import Debug.Trace

import Control.Concurrent
import Control.Concurrent.STM
import Data.HashMap.Strict (HashMap)
import Data.Hashable
import Data.Text (Text)
import qualified Data.Text as T
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word
import GHC.IO (unsafePerformIO)
import Language.Edh.EHI
import Language.Edh.LS.InsertTextFormat (InsertTextFormat)
import qualified Language.Edh.LS.InsertTextFormat as InsertTextFormat
import Language.Edh.LS.Json
import Language.Edh.LS.SymbolKind (SymbolKind)
import qualified Language.Edh.LS.SymbolKind as SymbolKind
import Prelude

type DocComment = [Text]

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

instance ToLSP EL'Diagnostic where
  toLSP
    ( EL'Diagnostic
        !rng
        !severity
        !code
        !source
        !msg
        !tags
      ) =
      jsonObject
        [ ("range", toLSP rng),
          ("severity", jsonInt severity),
          ( "code",
            case code of
              Left !i -> jsonInt i
              Right !s -> EdhString s
          ),
          ("source", EdhString source),
          ("message", EdhString msg),
          ( "tags",
            if null tags
              then nil
              else jsonArray' (EdhDecimal . fromIntegral) tags
          )
        ]

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

el'PrettyLoc :: EL'ModuSlot -> EL'Diagnostic -> Text
el'PrettyLoc !ms !diag =
  prettySrcRange
    (el'modu'doc ms)
    (el'diag'range diag)

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
    -- entry module. inclusive Edh fragments (i.e. ".iedh" files) are also
    -- categorized as scripts for the time being.
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
    -- | normalized name of the module
    -- this corresponds to `__name__` in the module at runtime
    -- relative import will fail if this is set to empty
    el'modu'name :: !Text,
    -- | absolute path of the `.edh` src file
    -- this corresponds to `__file__` in the module at runtime
    el'modu'doc :: !SrcDoc,
    -- | module source modified on-the-fly
    el'modu'src'otf :: !(TVar (Maybe (Int, Text, Word64))),
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
  = EL'ModuParsing !Int !(TMVar EL'ParsedModule)
  | EL'ModuParsed !EL'ParsedModule

data EL'ParsedModule = EL'ParsedModule
  { el'modu'src'version :: !Int,
    el'modu'doc'comment :: !OptDocCmt,
    el'modu'stmts :: ![StmtSrc],
    -- | diagnostics generated from this stage of analysis
    el'parsing'diags :: ![EL'Diagnostic]
  }

data EL'ResolvingModu = EL'ResolvingModu
  { -- | the thread doing the resolving
    el'resolving'thread :: !ThreadId,
    -- | all `extends` appeared in the direct scope and nested scopes (i.e.
    -- super modules), up to time of analysis
    el'modu'exts'wip :: !(TVar [EL'Value]),
    -- | exports from this module up-to-time of analysis
    el'modu'exps'wip :: !EL'ArtsWIP,
    -- | other modules this module depends on
    el'modu'dependencies'wip :: !(TVar (HashMap EL'ModuSlot Bool)),
    -- | diagnostics generated
    el'resolving'diags :: !(TVar [EL'Diagnostic]),
    -- | the same 'TVar' as el'modu'dependants
    el'resolving'dependants :: !(TVar (HashMap EL'ModuSlot Bool))
  }

data EL'ModuResolution
  = EL'ModuResolving !EL'ResolvingModu !(TMVar EL'ResolvedModule)
  | EL'ModuResolved !EL'ResolvedModule

data EL'ResolvedModule = EL'ResolvedModule
  { -- | there will be nested scopes appearing in natural source order, within
    -- this root scope of the module
    el'modu'scope :: !EL'Scope,
    -- | finalized exports from this module
    el'modu'exports :: !EL'Artifacts,
    -- | all attribute definitions in this module
    -- sorted so as they appear in source code
    el'modu'attr'defs :: !(Vector EL'AttrDef),
    -- | all attribute references in this module
    -- sorted so as they appear in source code
    el'modu'attr'refs :: !(Vector EL'AttrRef),
    -- | diagnostics generated during resolution
    el'resolution'diags :: ![EL'Diagnostic],
    -- | other modules this module depends on
    el'modu'dependencies :: !(HashMap EL'ModuSlot Bool),
    -- | other modules depending on this module, and defined with this revision
    -- of resolution for this module
    --
    -- the depdneant modules listed in this field should be invalidated alone
    -- with this module upon invalidation
    --
    -- note a dependant may stop depending on this module due to src changes,
    -- so cross checking of its `el'modu'dependencies` should be performed
    -- and honored, to avoid incorrect result due to race condition
    --
    -- TODO invalidaton of a dependency module tends to be a one-shot action,
    --      if a dependant is added after the invalidation is done, need some
    --      way to warrant proper invalidation of that dependant module.
    el'modu'dependants :: !(TVar (HashMap EL'ModuSlot Bool))
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
    el'attr'def'doc :: !OptDocCmt,
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

-- | get ultimate value
el'UltimateValue :: EL'Value -> EL'Value
el'UltimateValue = \case
  EL'External _msExt !defExt -> el'UltimateValue $ el'attr'def'value defExt
  !val -> val

-- | get ultimate value with original module
el'UltimateValue' :: EL'ModuSlot -> EL'Value -> (EL'ModuSlot, EL'Value)
el'UltimateValue' !ms = \case
  EL'External !msExt !defExt ->
    el'UltimateValue' msExt $ el'attr'def'value defExt
  !val -> (ms, val)

-- | get ultimate original definition of an attribute
el'UltimateDefi :: EL'ModuSlot -> EL'AttrDef -> (EL'ModuSlot, EL'AttrDef)
el'UltimateDefi ms !def = case el'attr'def'value def of
  EL'External !msExt !defExt -> el'UltimateDefi msExt defExt
  _ -> (ms, def)

-- | an annotation created by the (::) operator
data EL'AttrAnno = EL'AttrAnno
  { -- | right-hand expression to the (::) operator
    el'anno'expr :: !ExprSrc,
    -- | doc comment of the annotation
    -- this can show up on IDE hover, at least before we can generate more
    -- sophisticated descriptions for that
    el'anno'doc :: !OptDocCmt
  }

-- | 冇 annotation
maoAnnotation :: TVar (Maybe a)
maoAnnotation = unsafePerformIO $ newTVarIO Nothing
{-# NOINLINE maoAnnotation #-}

-- | an attribute reference, links a local addressor to its original definition
data EL'AttrRef
  = EL'UnsolvedRef !(Maybe EL'Value) !SrcRange
  | EL'AttrRef !(Maybe EL'Value) !AttrAddrSrc !EL'ModuSlot !EL'AttrDef
  deriving (Show)

el'AttrRefSpan :: EL'AttrRef -> SrcRange
el'AttrRefSpan (EL'UnsolvedRef _ !ref'span) = ref'span
el'AttrRefSpan (EL'AttrRef _ (AttrAddrSrc _ !ref'span) _ _) = ref'span

instance ToLSP EL'AttrRef where
  toLSP (EL'UnsolvedRef _ _) = jsonArray []
  toLSP ref@(EL'AttrRef _maybeTgtVal _attr !originModu !def) =
    if src'line (src'start $ el'attr'def'focus def) < 0
      then case el'attr'def'value def of -- hidden definition
        EL'External !fromModu !fromDef ->
          jsonArray $
            jsonObject
              [ ("originSelectionRange", toLSP $ el'AttrRefSpan ref),
                ("targetUri", toLSP $ el'modu'doc fromModu),
                ("targetRange", toLSP $ exprSrcSpan $ el'attr'def'expr fromDef),
                ("targetSelectionRange", toLSP $ el'attr'def'focus fromDef)
              ] :
            attrUpLinkChain fromDef
        _ -> jsonArray [] -- hidden yet not pointing to external value
      else
        jsonArray $
          jsonObject
            [ ("originSelectionRange", toLSP $ el'AttrRefSpan ref),
              ("targetUri", toLSP $ el'modu'doc originModu),
              ("targetRange", toLSP $ exprSrcSpan $ el'attr'def'expr def),
              ("targetSelectionRange", toLSP $ el'attr'def'focus def)
            ] :
          attrUpLinkChain def

attrUpLinkChain :: EL'AttrDef -> [EdhValue]
attrUpLinkChain !def = case el'attr'def'value def of
  EL'External !fromModu !fromDef ->
    if src'line (src'start $ el'attr'def'focus def) < 0
      then attrUpLinkChain fromDef -- hidden definition
      else
        jsonObject
          [ ("originSelectionRange", toLSP $ el'attr'def'focus def),
            ("targetUri", toLSP $ el'modu'doc fromModu),
            ("targetRange", toLSP $ exprSrcSpan $ el'attr'def'expr fromDef),
            ("targetSelectionRange", toLSP $ el'attr'def'focus fromDef)
          ] :
        attrUpLinkChain fromDef
  _ -> []

-- | doc-comments for an attribute encountered at all definition sites
data EL'AttrDoc = EL'AttrDoc !SrcRange ![DocComment]

instance ToLSP EL'AttrDoc where
  toLSP (EL'AttrDoc !attr'span !docs) =
    jsonObject
      [ ("range", toLSP attr'span),
        ( "contents",
          jsonObject
            [ ("kind", EdhString "markdown"),
              ("value", EdhString mdContents)
            ]
        )
      ]
    where
      !mdContents = T.intercalate "\n***\n" $ T.intercalate "\n" <$> docs

-- | collect all doc-comments from an attribute reference
el'AttrRefDoc :: EL'AttrRef -> EL'AttrDoc
el'AttrRefDoc ref@EL'UnsolvedRef {} = EL'AttrDoc (el'AttrRefSpan ref) []
el'AttrRefDoc ref@(EL'AttrRef _maybeTgtRef _attr _ms !tip) =
  EL'AttrDoc (el'AttrRefSpan ref) $ el'AttrDoc tip

el'AttrDefDoc :: EL'AttrDef -> EL'AttrDoc
el'AttrDefDoc !tip = EL'AttrDoc (el'attr'def'focus tip) $ el'AttrDoc tip

el'AttrDoc :: EL'AttrDef -> [DocComment]
el'AttrDoc = go []
  where
    go !docs !def = case el'attr'def'doc def of
      NoDocCmt -> go' docs
      DocCmt !doc -> go' (doc : docs)
      where
        go' !docs' = case el'attr'def'value def of
          EL'External _ms !def' -> go docs' def'
          _ -> reverse docs'

data EL'ArgsPack = EL'ArgsPack
  { el'apk'args :: ![EL'Value],
    el'apk'kwargs :: !(OrderedDict AttrKey EL'Value),
    el'apk'dyn'args :: !Bool,
    el'apk'dyn'kwargs :: !Bool
  }

instance Show EL'ArgsPack where
  show (EL'ArgsPack !args !kwargs !dyn'args !dyn'kwargs) =
    if null args && odNull kwargs && not dyn'args && not dyn'kwargs
      then "()"
      else
        "( " <> pos args <> kw (odToList kwargs)
          <> (if dyn'args then "*(), " else "")
          <> (if dyn'kwargs then "**(), " else "")
          <> ")"
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
    EL'ObjVal !EL'ModuSlot !EL'Object
  | -- | a class
    EL'ClsVal !EL'ModuSlot !EL'Class
  | -- | a module object
    EL'ModuVal !EL'ModuSlot
  | -- | a procedure
    EL'ProcVal !EL'ModuSlot !EL'Proc
  | -- | a property
    EL'PropVal !EL'ModuSlot !EL'Class !AttrKey
  | -- | result from a return stmt
    EL'Return !EL'Value
  | -- | result from a throw stmt
    EL'Throw !EL'Value
  | -- | result from a rethrow stmt
    EL'Rethrow
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
  show (EL'ObjVal _ms !obj) = "<object: " <> show (el'obj'class obj) <> ">"
  show (EL'ClsVal _ms !cls) = "<class: " <> show cls <> ">"
  show (EL'ModuVal !modu) = show modu
  show (EL'ProcVal _ms !p) = show p
  show (EL'PropVal _ms !cls !prop) = show cls <> "." <> show prop
  show (EL'Return !x) = show x
  show (EL'Throw !x) = show x
  show EL'Rethrow = "<rethrow>"
  show (EL'Expr !x) = show x

el'IsNil :: EL'Value -> Bool
el'IsNil (EL'Const EdhNil) = True
el'IsNil _ = False

-- | a procedure
data EL'Proc = EL'Proc
  { el'proc'name :: AttrKey,
    el'proc'args :: !ArgsReceiver
  }
  deriving (Show)

-- | an object
--
-- objects are intrinsically mutable, it has to be kept open during analysis,
-- and unfortunately has to even remain so after the analysis is done
data EL'Object = EL'Object
  { el'obj'class :: !EL'Class,
    el'obj'attrs :: !EL'ArtsWIP,
    el'obj'exts :: !(TVar [EL'Value]),
    el'obj'exps :: !EL'ArtsWIP
  }

el'ObjNew :: EL'Class -> STM EL'Object
el'ObjNew !cls = do
  !objAttrs <- iopdClone $ el'inst'attrs cls
  !objExts <- newTVar []
  !objExps <- iopdEmpty
  return $ EL'Object cls objAttrs objExts objExps

-- | a class
--
-- a class has its attributes and exports mutable during analysis
--
-- note the `supers` list of an object at runtime is instances created
-- according to its class' `mro` list, plus more super objects appended
-- by `extends` statements, usually from within the `__init__()` method
-- (though dynamic `extends` from arbitrary methods whenever called is also
-- allowed)
data EL'Class = EL'Class
  { -- | class name
    el'class'name :: !AttrKey,
    -- | meta class
    -- note this field can not be strict
    el'class'meta :: EL'Class,
    -- | only filled after fully defined
    el'class'defi :: !(TMVar EL'ClassDefi),
    -- | all attributes of the class
    el'class'attrs :: !EL'ArtsWIP,
    -- | super classes installed via @extends@ from class defining procedure
    el'class'exts :: !(TVar [EL'Value]),
    -- | attributes exported from the class defining procedure
    el'class'exps :: !EL'ArtsWIP,
    -- | instance attributes ever assigned via @this.xxx@ from methods (esp.
    -- @__init__()@), also include data fields for data classes
    el'inst'attrs :: !EL'ArtsWIP,
    -- | super instances ever installed via @extends@ from methods (esp.
    -- @__init__()@)
    el'inst'exts :: !(TVar [EL'Value]),
    -- | attributes ever exported from methods (esp. @__init__()@)
    el'inst'exps :: !EL'ArtsWIP
  }

instance Show EL'Class where
  show !cls = show $ el'class'name cls

data EL'ClassDefi = EL'ClassDefi
  { -- | C3 linearized mro list
    el'class'mro :: ![EL'Class],
    -- | scope of the class defining procedure
    el'class'scope :: !EL'Scope,
    -- | annotations from the class defining procedure
    el'class'annos :: !(OrderedDict AttrKey EL'AttrAnno)
  }

el'ResolveObjAttr :: EL'Object -> AttrKey -> STM (Maybe EL'AttrDef)
el'ResolveObjAttr !obj !key =
  iopdLookup key (el'obj'attrs obj) >>= \case
    result@Just {} -> return result
    Nothing -> el'ResolveObjAttr' (el'obj'class obj) key

el'ResolveObjAttr' :: EL'Class -> AttrKey -> STM (Maybe EL'AttrDef)
el'ResolveObjAttr' !cls !key =
  (go . (cls :) =<<) $
    tryReadTMVar (el'class'defi cls) >>= \case
      Nothing -> return []
      Just (EL'ClassDefi !mro _scope _annos) -> return mro
  where
    go [] = return Nothing
    go (c : rest) =
      iopdLookup key (el'inst'attrs c) >>= \case
        Just !def -> return $ Just def
        Nothing ->
          iopdLookup key (el'class'attrs c) >>= \case
            Just !def -> return $ Just def
            Nothing -> go rest

_EmptyArts :: EL'ArtsWIP
_EmptyArts = unsafePerformIO iopdEmptyIO
{-# NOINLINE _EmptyArts #-}

_EmptyExts :: TVar [EL'Value]
_EmptyExts = unsafePerformIO $ newTVarIO []
{-# NOINLINE _EmptyExts #-}

_EmptyClsDefi :: TMVar EL'ClassDefi
_EmptyClsDefi =
  unsafePerformIO $
    newTMVarIO $
      EL'ClassDefi
        []
        ( EL'Scope
            noSrcRange
            V.empty
            V.empty
        )
        odEmpty
{-# NOINLINE _EmptyClsDefi #-}

el'MetaClass :: EL'Class
el'MetaClass = mc
  where
    mc =
      EL'Class
        (AttrByName "class")
        mc -- meta of meta is itself
        _EmptyClsDefi
        _EmptyArts
        _EmptyExts
        _EmptyArts
        _EmptyArts
        _EmptyExts
        _EmptyArts

el'NamespaceClass :: EL'Class
el'NamespaceClass =
  EL'Class
    (AttrByName "<namespace>")
    el'MetaClass
    _EmptyClsDefi
    _EmptyArts
    _EmptyExts
    _EmptyArts
    _EmptyArts
    _EmptyExts
    _EmptyArts

el'ModuleClass :: EL'Class
el'ModuleClass =
  EL'Class
    (AttrByName "<module>")
    el'MetaClass
    _EmptyClsDefi
    _EmptyArts
    _EmptyExts
    _EmptyArts
    _EmptyArts
    _EmptyExts
    _EmptyArts

el'ScopeClass :: EL'Class
el'ScopeClass =
  EL'Class
    (AttrByName "<scope>")
    el'MetaClass
    _EmptyClsDefi
    _EmptyArts
    _EmptyExts
    _EmptyArts
    _EmptyArts
    _EmptyExts
    _EmptyArts

-- | a scope is backed by an entity with arbitrary attributes, as Edh allows
-- very straight forward sharing of lexical scopes to goroutines spawned from
-- within an inner scope, it may be more right to assume all attributes ever
-- defined in outer scopes are accessible, before precise concurrent flow
-- analysis is performed
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
    el'scope'regions :: !(Vector EL'Region)
  }
  deriving (Show)

-- | 冇 scope
maoScope :: EL'Scope
maoScope = EL'Scope noSrcRange V.empty V.empty

el'ScopeAttrs :: EL'Scope -> EL'Artifacts
el'ScopeAttrs =
  odFromList . concatMap (odToList . el'region'attrs)
    . V.toList
    . el'scope'regions

collectArtsInScopeAt :: SrcPos -> EL'Scope -> [(AttrKey, EL'AttrDef)]
collectArtsInScopeAt !pos !tip = case go [] tip of
  Left !outers ->
    concat $
      odToList . el'ScopeAttrs <$> outers
  Right (!outers, EL'Region _ !reg'arts) ->
    concat $
      odToList reg'arts :
      (odToList . el'ScopeAttrs <$> outers)
  where
    go :: [EL'Scope] -> EL'Scope -> Either [EL'Scope] ([EL'Scope], EL'Region)
    go !outers scope@(EL'Scope !scope'span !inners !regions) =
      case srcPosCmp2Range pos scope'span of
        LT -> Left outers
        GT -> Left outers
        EQ -> case searchInners (V.toList inners) of
          Just !region -> Right (scope : outers, region)
          Nothing -> case locateRegion Nothing (V.toList regions) of
            Nothing -> Left outers
            Just !region -> Right (outers, region)

    -- TODO use binary search for performance
    locateRegion :: Maybe EL'Region -> [EL'Region] -> Maybe EL'Region
    locateRegion !prev [] = prev
    locateRegion !prev (r : rest) = case compare pos $ el'region'start r of
      LT -> prev
      EQ -> locateRegion (Just r) rest
      GT -> locateRegion (Just r) rest

    -- TODO use binary search for performance
    searchInners :: [EL'Scope] -> Maybe EL'Region
    searchInners [] = Nothing
    searchInners (s : rest) =
      case srcPosCmp2Range pos $ el'scope'span s of
        LT -> Nothing
        EQ -> locateRegion Nothing (V.toList $ el'scope'regions s)
        GT -> searchInners rest

-- | a region records attributes available within it
data EL'Region = EL'Region
  { el'region'start :: !SrcPos,
    -- | available attributes defined in this region
    el'region'attrs :: !EL'Artifacts
  }
  deriving (Show)

regionKey :: EL'Region -> SrcPos
regionKey = el'region'start

type EL'Artifacts = OrderedDict AttrKey EL'AttrDef

instance Show EL'Artifacts where
  show _arts = "<artifacts>"

attrDefKey :: EL'AttrDef -> SrcPos
attrDefKey !def = src'end $ el'attr'def'focus def

attrRefKey :: EL'AttrRef -> SrcPos
attrRefKey !ref = src'end $ el'AttrRefSpan ref

locateAttrDefInModule :: Int -> Int -> EL'ResolvedModule -> Maybe EL'AttrDef
locateAttrDefInModule !line !char !modu =
  locateSym $ -- TODO use binary search for performance with large modules
    V.toList $ el'modu'attr'defs modu
  where
    !p = SrcPos line char

    locateSym :: [EL'AttrDef] -> Maybe EL'AttrDef
    locateSym [] = Nothing
    locateSym (def : rest) = case srcPosCmp2Range p $ el'attr'def'focus def of
      EQ -> Just def
      LT -> Nothing
      GT -> locateSym rest

locateAttrRefInModule :: Int -> Int -> EL'ResolvedModule -> Maybe EL'AttrRef
locateAttrRefInModule !line !char !modu =
  locateRef $ -- TODO use binary search for performance with large modules
    V.toList $ el'modu'attr'refs modu
  where
    !p = SrcPos line char

    locateRef :: [EL'AttrRef] -> Maybe EL'AttrRef
    locateRef [] = Nothing
    locateRef (ref : rest) =
      let !ref'span = el'AttrRefSpan ref
       in case srcPosCmp2Range p ref'span of
            EQ -> Just ref
            LT -> Nothing
            GT -> locateRef rest

data TextEdit = TextEdit
  { el'te'range :: !SrcRange,
    el'te'newText :: !Text
  }

instance ToLSP TextEdit where
  toLSP (TextEdit !range !newText) =
    jsonObject
      [ ("range", toLSP range),
        ("newText", EdhString newText)
      ]

-- * Hierarchical Symbols for Outline

data DocumentSymbol = DocumentSymbol
  { el'sym'name :: !Text,
    el'sym'detail :: !Text,
    el'sym'kind :: !SymbolKind,
    el'sym'range :: !SrcRange,
    el'sym'selectionRange :: !SrcRange,
    el'sym'children :: ![DocumentSymbol]
  }

instance ToLSP DocumentSymbol where
  toLSP (DocumentSymbol !name !detail !kind !range !selectionRange !children) =
    jsonObject
      [ ("name", EdhString name),
        ("detail", EdhString detail),
        ("kind", toLSP kind),
        ("range", toLSP range),
        ("selectionRange", toLSP selectionRange),
        ("children", jsonArray $ toLSP <$> children)
      ]

titledBlock ::
  DocComment ->
  SrcRange ->
  [DocumentSymbol] ->
  DocumentSymbol
titledBlock
  !cmt
  range@(SrcRange (SrcPos !start'line !start'char) _)
  !exprSymbols =
    DocumentSymbol
      { el'sym'name = name,
        el'sym'detail = detail,
        el'sym'kind = SymbolKind.Namespace,
        el'sym'range = range,
        el'sym'selectionRange = SrcRange startPos startPos,
        el'sym'children = exprSymbols
      }
    where
      -- selection start at the position immediately following `{##`
      !startPos = SrcPos start'line (start'char + 3)

      decorTitle !t = case T.strip t of
        "" -> "<untitled>"
        !title -> title

      (name, detail) = case cmt of
        [] -> ("<untitled>", "")
        line1 : line2 : _ -> (decorTitle line1, line2)
        line1 : _ -> (decorTitle line1, "")

procDecl ::
  OptDocCmt ->
  AttrAddrSrc ->
  SymbolKind ->
  SrcRange ->
  [DocumentSymbol] ->
  DocumentSymbol
procDecl
  !cmt
  (AttrAddrSrc !name !name'span)
  !kind
  !range
  !exprSymbols =
    DocumentSymbol
      { el'sym'name = attrAddrStr name,
        el'sym'detail = detail,
        el'sym'kind = kind,
        el'sym'range = range,
        el'sym'selectionRange = name'span,
        el'sym'children = exprSymbols
      }
    where
      detail = case cmt of
        NoDocCmt -> ""
        DocCmt [] -> ""
        DocCmt (line1 : _) -> line1

moduSymbols :: Text -> OptDocCmt -> [StmtSrc] -> [DocumentSymbol]
moduSymbols !name !cmt !stmts = [moduSym]
  where
    !moduSym =
      DocumentSymbol
        { el'sym'name = name,
          el'sym'detail = detail,
          el'sym'kind = SymbolKind.Module,
          el'sym'range = range,
          el'sym'selectionRange = selRange,
          el'sym'children = blockSymbols stmts
        }
    !detail = case cmt of
      DocCmt (line1 : _) -> line1
      _ -> ""
    (!range, !selRange) = case stmts of
      [] -> (zeroSrcRange, zeroSrcRange)
      (StmtSrc _ (SrcRange !startPos1 !endPos1)) : rest ->
        ( SrcRange beginningSrcPos $ endPos endPos1 rest,
          SrcRange beginningSrcPos startPos1
        )
    endPos :: SrcPos -> [StmtSrc] -> SrcPos
    endPos !p [] = p
    endPos _ ((StmtSrc _ (SrcRange _ !p)) : more) = endPos p more

blockSymbols :: [StmtSrc] -> [DocumentSymbol]
blockSymbols !stmts = concat $ stmtSymbols <$> stmts
  where
    stmtSymbols :: StmtSrc -> [DocumentSymbol]
    stmtSymbols (StmtSrc (ExprStmt !x !doc) !stmt'span) =
      exprSymbols doc stmt'span x
    stmtSymbols (StmtSrc (GoStmt !x) _) = exprSymbols' NoDocCmt x
    stmtSymbols (StmtSrc (DeferStmt !x) _) = exprSymbols' NoDocCmt x
    stmtSymbols (StmtSrc (LetStmt _ (ArgsPacker !sndrs _)) _) =
      concat $ exprSymbols' NoDocCmt . sentArgExprSrc <$> sndrs
    stmtSymbols (StmtSrc (ExtendsStmt !x) _) = exprSymbols' NoDocCmt x
    stmtSymbols (StmtSrc (PerceiveStmt !x !stmt) _) =
      exprSymbols' NoDocCmt x ++ stmtSymbols stmt
    stmtSymbols (StmtSrc (ThrowStmt !x) _) = exprSymbols' NoDocCmt x
    stmtSymbols (StmtSrc (ReturnStmt !x _docCmt) _) = exprSymbols' NoDocCmt x
    stmtSymbols _ = []

    exprSymbols' :: OptDocCmt -> ExprSrc -> [DocumentSymbol]
    exprSymbols' !doc (ExprSrc !x !expr'span) = exprSymbols doc expr'span x

    exprSymbols'' :: OptDocCmt -> SrcRange -> ExprSrc -> [DocumentSymbol]
    exprSymbols'' !doc !full'span (ExprSrc !x _) = exprSymbols doc full'span x

    exprSymbols :: OptDocCmt -> SrcRange -> Expr -> [DocumentSymbol]
    exprSymbols !doc !full'span (BlockExpr !nested'stmts) = case doc of
      DocCmt !cmt -> [titledBlock cmt full'span $ blockSymbols nested'stmts]
      NoDocCmt -> blockSymbols nested'stmts
    exprSymbols !doc !full'span (ScopedBlockExpr !nested'stmts) = case doc of
      DocCmt !cmt -> [titledBlock cmt full'span $ blockSymbols nested'stmts]
      NoDocCmt -> blockSymbols nested'stmts
    exprSymbols
      !doc
      !full'span
      (NamespaceExpr (ProcDecl !name _args !body _loc) (ArgsPacker !sndrs _)) =
        [ procDecl doc name SymbolKind.Namespace full'span $
            concat (exprSymbols' NoDocCmt . sentArgExprSrc <$> sndrs)
              ++ stmtSymbols body
        ]
    exprSymbols
      !doc
      !full'span
      (ClassExpr (ProcDecl !name _args !body _loc)) =
        [procDecl doc name SymbolKind.Class full'span $ stmtSymbols body]
    exprSymbols
      !doc
      !full'span
      (MethodExpr (ProcDecl !name _args !body _loc)) =
        [procDecl doc name SymbolKind.Method full'span $ stmtSymbols body]
    exprSymbols
      !doc
      !full'span
      (GeneratorExpr (ProcDecl !name _args !body _loc)) =
        [procDecl doc name SymbolKind.Method full'span $ stmtSymbols body]
    exprSymbols
      !doc
      !full'span
      (InterpreterExpr (ProcDecl !name _args !body _loc)) =
        [procDecl doc name SymbolKind.Method full'span $ stmtSymbols body]
    exprSymbols
      !doc
      !full'span
      (ProducerExpr (ProcDecl !name _args !body _loc)) =
        [procDecl doc name SymbolKind.Method full'span $ stmtSymbols body]
    exprSymbols
      !doc
      !full'span
      (OpDefiExpr _ _ _ (ProcDecl !name _args !body _loc)) =
        [procDecl doc name SymbolKind.Operator full'span $ stmtSymbols body]
    exprSymbols
      !doc
      !full'span
      (OpOvrdExpr _ _ _ (ProcDecl !name _args !body _loc)) =
        [procDecl doc name SymbolKind.Operator full'span $ stmtSymbols body]
    exprSymbols !doc _full'span (VoidExpr !x) = exprSymbols' doc x
    exprSymbols !doc _full'span (AtoIsoExpr !x) = exprSymbols' doc x
    exprSymbols !doc _full'span (PrefixExpr _ !x) = exprSymbols' doc x
    exprSymbols !doc _full'span (IfExpr !cnd !cseq !alt) =
      exprSymbols' doc cnd ++ stmtSymbols cseq ++ maybe [] stmtSymbols alt
    exprSymbols !doc _full'span (CaseExpr !t !b) =
      exprSymbols' doc t ++ exprSymbols' doc b
    exprSymbols !doc _full'span (DictExpr !entries) = concat $
      (<$> entries) $ \(!k, !v) -> (++ exprSymbols' doc v) $ case k of
        ExprDictKey !x -> exprSymbols' doc x
        _ -> []
    exprSymbols !doc _full'span (ListExpr !items) =
      concat $ exprSymbols' doc <$> items
    exprSymbols !doc _full'span (ArgsPackExpr (ArgsPacker !sndrs _)) =
      concat $ exprSymbols' doc . sentArgExprSrc <$> sndrs
    exprSymbols !doc !full'span (ParenExpr !x) = exprSymbols'' doc full'span x
    exprSymbols !doc _full'span (IncludeExpr !src) = exprSymbols' doc src
    exprSymbols !doc _full'span (ImportExpr _ !src !into) =
      exprSymbols' doc src ++ maybe [] (exprSymbols' doc) into
    exprSymbols !doc !full'span (ExportExpr !x) = exprSymbols'' doc full'span x
    exprSymbols !doc _full'span (YieldExpr !x) = exprSymbols' doc x
    exprSymbols !doc _full'span (ForExpr _scoped _rcvrs !from !body) =
      exprSymbols' doc from ++ stmtSymbols body
    exprSymbols !doc _full'span (WhileExpr !x !stmt) =
      exprSymbols' doc x ++ stmtSymbols stmt
    exprSymbols !doc _full'span (DoWhileExpr !stmt !x) =
      stmtSymbols stmt ++ exprSymbols' doc x
    exprSymbols !doc _full'span (IndexExpr !idx !tgt) =
      exprSymbols' doc tgt ++ exprSymbols' doc idx
    exprSymbols !doc _full'span (CallExpr !callee (ArgsPacker !sndrs _)) =
      concat (exprSymbols' doc . sentArgExprSrc <$> sndrs)
        ++ exprSymbols' doc callee
    exprSymbols !doc _full'span (InfixExpr _op !lhs !rhs) =
      exprSymbols' doc lhs ++ exprSymbols' doc rhs
    exprSymbols !doc _full'span (DefaultExpr Nothing !x) = exprSymbols' doc x
    exprSymbols !doc _full'span (DefaultExpr (Just (ArgsPacker !sndrs _)) !x) =
      (++ exprSymbols' doc x) $
        concat $ exprSymbols' doc . sentArgExprSrc <$> sndrs
    exprSymbols !doc _full'span (ExprWithSrc !x !ssegs) =
      (exprSymbols' doc x ++) $
        concat $
          (<$> ssegs) $ \case
            SrcSeg _txt -> []
            IntplSeg !x' -> exprSymbols' doc x'
    exprSymbols !doc _full'span (IntplExpr !x) = exprSymbols' doc x
    exprSymbols _ _ _ = []

-- * Folding of Hierarchical Symbols

data FoldingRange = FoldingRange
  { el'fold'startLine :: !Int,
    el'fold'startCharacter :: !Int,
    el'fold'endLine :: !Int,
    el'fold'endCharacter :: !Int,
    el'fold'kind :: !Text
  }

instance ToLSP FoldingRange where
  toLSP (FoldingRange !startLine !startCharacter !endLine !endCharacter !kind) =
    jsonObject
      [ ("startLine", jsonInt startLine),
        ("startCharacter", jsonInt startCharacter),
        ("endLine", jsonInt endLine),
        ("endCharacter", jsonInt endCharacter),
        ("kind", if T.null kind then nil else EdhString kind)
      ]

foldingRange :: SrcRange -> FoldingRange
foldingRange !rng = foldingRange' rng "region"

foldingRange' :: SrcRange -> Text -> FoldingRange
foldingRange'
  (SrcRange (SrcPos !start'line !start'char) (SrcPos !end'line !end'char))
  !kind =
    FoldingRange
      { el'fold'startLine = start'line,
        el'fold'startCharacter = start'char,
        el'fold'endLine = end'line,
        el'fold'endCharacter = end'char,
        el'fold'kind = kind
      }

blockFoldRngs :: [StmtSrc] -> [FoldingRange]
blockFoldRngs [] = []
blockFoldRngs (stmt1 : more'stmts) = foldGap stmt1 more'stmts
  where
    foldGap :: StmtSrc -> [StmtSrc] -> [FoldingRange]
    foldGap !stmt [] = stmtFoldRngs stmt
    foldGap !stmt (next'stmt : rest'stmts) = case stmtFoldRngs stmt of
      [] -> more'rngs
      lead'rngs@(rng : rngs) ->
        let last'end'line =
              foldl max (el'fold'endLine rng) $ el'fold'endLine <$> rngs
         in case more'rngs of
              [] -> lead'rngs
              next'rng : _ ->
                lead'rngs
                  ++ gapRngs last'end'line next'rng
                  ++ more'rngs
      where
        gapRngs
          !last'end'line
          (FoldingRange !next'start'line _ _ _ _) =
            [ foldingRange'
                ( SrcRange
                    (SrcPos (last'end'line + 1) 0)
                    (SrcPos (next'start'line - 1) 0)
                )
                "" -- region kind for verbose details here?
              | next'start'line - last'end'line > 5
            ]
        more'rngs = foldGap next'stmt rest'stmts

    stmtFoldRngs :: StmtSrc -> [FoldingRange]
    stmtFoldRngs (StmtSrc (ExprStmt !x _doc) !stmt'span) =
      exprFoldRngs stmt'span x
    stmtFoldRngs (StmtSrc (GoStmt !x) _) = exprFoldRngs' x
    stmtFoldRngs (StmtSrc (DeferStmt !x) _) = exprFoldRngs' x
    stmtFoldRngs (StmtSrc (LetStmt _ (ArgsPacker !sndrs _)) _) =
      concat $ exprFoldRngs' . sentArgExprSrc <$> sndrs
    stmtFoldRngs (StmtSrc (ExtendsStmt !x) _) = exprFoldRngs' x
    stmtFoldRngs (StmtSrc (PerceiveStmt !x !stmt) _) =
      exprFoldRngs' x ++ stmtFoldRngs stmt
    stmtFoldRngs (StmtSrc (ThrowStmt !x) _) = exprFoldRngs' x
    stmtFoldRngs (StmtSrc (ReturnStmt !x _docCmt) _) = exprFoldRngs' x
    stmtFoldRngs _ = []

    exprFoldRngs' :: ExprSrc -> [FoldingRange]
    exprFoldRngs' (ExprSrc !x !expr'span) = exprFoldRngs expr'span x

    exprFoldRngs'' :: SrcRange -> ExprSrc -> [FoldingRange]
    exprFoldRngs'' !full'span (ExprSrc !x _) = exprFoldRngs full'span x

    exprFoldRngs :: SrcRange -> Expr -> [FoldingRange]
    exprFoldRngs !full'span (BlockExpr !nested'stmts) =
      foldingRange full'span : blockFoldRngs nested'stmts
    exprFoldRngs !full'span (ScopedBlockExpr !nested'stmts) =
      foldingRange full'span : blockFoldRngs nested'stmts
    exprFoldRngs
      !full'span
      (NamespaceExpr (ProcDecl _name _args !body _loc) _apkr) =
        foldingRange full'span : stmtFoldRngs body
    exprFoldRngs
      !full'span
      (ClassExpr (ProcDecl _name _args !body _loc)) =
        foldingRange full'span : stmtFoldRngs body
    exprFoldRngs
      !full'span
      (MethodExpr (ProcDecl _name _args !body _loc)) =
        foldingRange full'span : stmtFoldRngs body
    exprFoldRngs
      !full'span
      (GeneratorExpr (ProcDecl _name _args !body _loc)) =
        foldingRange full'span : stmtFoldRngs body
    exprFoldRngs
      !full'span
      (InterpreterExpr (ProcDecl _name _args !body _loc)) =
        foldingRange full'span : stmtFoldRngs body
    exprFoldRngs
      !full'span
      (ProducerExpr (ProcDecl _name _args !body _loc)) =
        foldingRange full'span : stmtFoldRngs body
    exprFoldRngs
      !full'span
      (OpDefiExpr _ _ _ (ProcDecl _name _args !body _loc)) =
        foldingRange full'span : stmtFoldRngs body
    exprFoldRngs
      !full'span
      (OpOvrdExpr _ _ _ (ProcDecl _name _args !body _loc)) =
        foldingRange full'span : stmtFoldRngs body
    exprFoldRngs _full'span (VoidExpr !x) = exprFoldRngs' x
    exprFoldRngs _full'span (AtoIsoExpr !x) = exprFoldRngs' x
    exprFoldRngs _full'span (PrefixExpr _ !x) = exprFoldRngs' x
    exprFoldRngs _full'span (IfExpr !cnd !cseq !alt) =
      exprFoldRngs' cnd ++ stmtFoldRngs cseq ++ maybe [] stmtFoldRngs alt
    exprFoldRngs _full'span (CaseExpr !t !b) =
      exprFoldRngs' t ++ exprFoldRngs' b
    exprFoldRngs _full'span (DictExpr !entries) = concat $
      (<$> entries) $ \(!k, !v) -> (++ exprFoldRngs' v) $ case k of
        ExprDictKey !x -> exprFoldRngs' x
        _ -> []
    exprFoldRngs _full'span (ListExpr !items) =
      concat $ exprFoldRngs' <$> items
    exprFoldRngs _full'span (ArgsPackExpr (ArgsPacker !sndrs _)) =
      concat $ exprFoldRngs' . sentArgExprSrc <$> sndrs
    exprFoldRngs !full'span (ParenExpr !x) = exprFoldRngs'' full'span x
    exprFoldRngs _full'span (IncludeExpr !src) = exprFoldRngs' src
    exprFoldRngs _full'span (ImportExpr _ !src !into) =
      exprFoldRngs' src ++ maybe [] exprFoldRngs' into
    exprFoldRngs !full'span (ExportExpr !x) = exprFoldRngs'' full'span x
    exprFoldRngs _full'span (YieldExpr !x) = exprFoldRngs' x
    exprFoldRngs _full'span (ForExpr _scoped _rcvrs !from !body) =
      exprFoldRngs' from ++ stmtFoldRngs body
    exprFoldRngs _full'span (WhileExpr !x !stmt) =
      exprFoldRngs' x ++ stmtFoldRngs stmt
    exprFoldRngs _full'span (DoWhileExpr !stmt !x) =
      stmtFoldRngs stmt ++ exprFoldRngs' x
    exprFoldRngs _full'span (IndexExpr !idx !tgt) =
      exprFoldRngs' tgt ++ exprFoldRngs' idx
    exprFoldRngs _full'span (CallExpr !callee (ArgsPacker !sndrs _)) =
      concat (exprFoldRngs' . sentArgExprSrc <$> sndrs)
        ++ exprFoldRngs' callee
    exprFoldRngs _full'span (InfixExpr _op !lhs !rhs) =
      exprFoldRngs' lhs ++ exprFoldRngs' rhs
    exprFoldRngs _full'span (DefaultExpr Nothing !x) = exprFoldRngs' x
    exprFoldRngs _full'span (DefaultExpr (Just (ArgsPacker !sndrs _)) !x) =
      (++ exprFoldRngs' x) $ concat $ exprFoldRngs' . sentArgExprSrc <$> sndrs
    exprFoldRngs _full'span (ExprWithSrc !x !ssegs) =
      (exprFoldRngs' x ++) $
        concat $
          (<$> ssegs) $ \case
            SrcSeg _txt -> []
            IntplSeg !x' -> exprFoldRngs' x'
    exprFoldRngs _full'span (IntplExpr !x) = exprFoldRngs' x
    exprFoldRngs _ _ = []

-- * Completion / Suggestion

data CompletionItem = CompletionItem
  { el'cmpl'label :: !Text,
    el'cmpl'detail :: !Text,
    el'cmpl'documentation :: !Text, -- in markdown format
    el'cmpl'preselect :: !Bool,
    el'cmpl'sortText :: !Text,
    el'cmpl'filterText :: !Text,
    el'cmpl'insertText :: !Text,
    el'cmpl'insertTextFormat :: !InsertTextFormat,
    el'cmpl'textEdit :: !TextEdit
  }

instance ToLSP CompletionItem where
  toLSP
    ( CompletionItem
        !label
        !detail
        !doc
        !presel
        !st
        !fl
        !ins
        !fmt
        te@(TextEdit (SrcRange (SrcPos !start'line _start'col) _end'pos) _)
      ) =
      jsonObject
        [ ("label", EdhString label),
          ("detail", EdhString detail),
          ("documentation", EdhString doc),
          ("preselect", EdhBool presel),
          ("sortText", if T.null st then EdhNil else EdhString st),
          ("filterText", if T.null fl then EdhNil else EdhString fl),
          ("insertText", if T.null ins then EdhNil else EdhString ins),
          ("insertTextFormat", toLSP fmt),
          ("textEdit", if start'line < 0 then EdhNil else toLSP te)
        ]

completionText :: Text -> Text -> Text -> Text -> SrcRange -> CompletionItem
completionText !label !detail !doc !cate !replace'span =
  CompletionItem
    label
    detail
    doc
    False
    (cate <> ":" <> label)
    ""
    ""
    InsertTextFormat.PlainText
    (TextEdit replace'span label)

completionToken ::
  Text ->
  Text ->
  Text ->
  Text ->
  CompletionItem
completionToken !label !detail !doc !cate =
  CompletionItem
    label
    detail
    doc
    False
    (cate <> ":" <> label)
    ""
    ""
    InsertTextFormat.PlainText
    (TextEdit noSrcRange "")

completionSnippet ::
  Text ->
  Text ->
  Text ->
  Text ->
  Text ->
  CompletionItem
completionSnippet !label !detail !doc !cate !snippet =
  CompletionItem
    label
    detail
    doc
    False
    (cate <> ":" <> label)
    label
    snippet
    InsertTextFormat.Snippet
    (TextEdit noSrcRange "")
