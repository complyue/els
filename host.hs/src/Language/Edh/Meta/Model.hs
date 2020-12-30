module Language.Edh.Meta.Model where

-- import           Debug.Trace

import Control.Concurrent
import Control.Concurrent.STM
import Data.HashMap.Strict (HashMap)
import Data.Hashable
import Data.Text (Text)
import qualified Data.Text as T
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.IO (unsafePerformIO)
import Language.Edh.EHI
import Language.Edh.LS.Json
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
    -- | normalized name of the module
    -- this corresponds to `__name__` in the module at runtime
    -- relative import will fail if this is set to empty
    el'modu'name :: !Text,
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
  = EL'ModuParsing !(TMVar EL'ParsedModule)
  | EL'ModuParsed !EL'ParsedModule

data EL'ParsedModule = EL'ParsedModule
  { el'modu'doc'comment :: !(Maybe DocComment),
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
    el'attr'def'doc :: !(Maybe DocComment),
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
    el'anno'doc :: !(Maybe DocComment)
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
      Nothing -> go' docs
      Just !doc -> go' (doc : docs)
      where
        go' !docs' = case el'attr'def'value def of
          EL'External _ms !def' -> go docs' def'
          _ -> reverse docs'

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
    -- | super classes installed via @extends@ from class defining procedure
    el'class'exts :: ![EL'Value],
    -- | C3 linearized mro list
    el'class'mro :: ![EL'Class],
    -- | scope of the class defining procedure
    el'class'scope :: !EL'Scope,
    -- | all attributes of the class
    el'class'attrs :: !EL'Artifacts,
    -- | attributes exported from the class defining procedure
    el'class'exps :: !EL'Artifacts,
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

el'ResolveObjAttr :: EL'Object -> AttrKey -> STM (Maybe EL'AttrDef)
el'ResolveObjAttr !obj !key =
  iopdLookup key (el'obj'attrs obj) >>= \case
    result@Just {} -> return result
    Nothing -> el'ResolveObjAttr' (el'obj'class obj) key

el'ResolveObjAttr' :: EL'Class -> AttrKey -> STM (Maybe EL'AttrDef)
el'ResolveObjAttr' !cls !key = go $ cls : el'class'mro cls
  where
    go [] = return Nothing
    go (c : rest) =
      iopdLookup key (el'inst'attrs c) >>= \case
        Just !def -> return $ Just def
        Nothing -> case odLookup key $ el'class'attrs c of
          Just !def -> return $ Just def
          Nothing -> go rest

_EmptyArts :: EL'ArtsWIP
_EmptyArts = unsafePerformIO iopdEmptyIO
{-# NOINLINE _EmptyArts #-}

_EmptyExts :: TVar [EL'Value]
_EmptyExts = unsafePerformIO $ newTVarIO []
{-# NOINLINE _EmptyExts #-}

el'MetaClass :: EL'Class
el'MetaClass = mc
  where
    mc =
      EL'Class
        (AttrByName "class")
        mc -- meta of meta is itself
        []
        []
        ( EL'Scope
            noSrcRange
            V.empty
            V.empty
        )
        odEmpty
        odEmpty
        _EmptyArts
        _EmptyExts
        _EmptyArts

el'NamespaceClass :: EL'Class
el'NamespaceClass =
  EL'Class
    (AttrByName "<namespace>")
    el'MetaClass
    []
    []
    maoScope
    odEmpty
    odEmpty
    _EmptyArts
    _EmptyExts
    _EmptyArts

el'ModuleClass :: EL'Class
el'ModuleClass =
  EL'Class
    (AttrByName "<module>")
    el'MetaClass
    []
    []
    maoScope
    odEmpty
    odEmpty
    _EmptyArts
    _EmptyExts
    _EmptyArts

el'ScopeClass :: EL'Class
el'ScopeClass =
  EL'Class
    (AttrByName "<scope>")
    el'MetaClass
    []
    []
    maoScope
    odEmpty
    odEmpty
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

-- | a region records attributes available within it
data EL'Region = EL'Region
  { el'region'span :: !SrcRange,
    -- | available attributes defined in this region
    el'region'attrs :: !EL'Artifacts
  }
  deriving (Show)

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

data CompletionItem = CompletionItem
  { el'cmpl'label :: !Text,
    el'cmpl'detail :: !Text,
    el'cmpl'documentation :: !Text, -- in markdown format
    el'cmpl'preselect :: !Bool,
    el'cmpl'sortText :: Text,
    el'cmpl'textEdit :: !TextEdit
  }

instance ToLSP CompletionItem where
  toLSP (CompletionItem !label !detail !doc !presel !st !te) =
    jsonObject
      [ ("label", EdhString label),
        ("detail", EdhString detail),
        ("documentation", EdhString doc),
        ("preselect", EdhBool presel),
        ("sortText", EdhString st),
        ("textEdit", toLSP te)
      ]
