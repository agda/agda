{-# LANGUAGE CPP                  #-}
{-# LANGUAGE UndecidableInstances #-}

{-| Translation from "Agda.Syntax.Concrete" to "Agda.Syntax.Abstract". Involves scope analysis,
    figuring out infix operator precedences and tidying up definitions.
-}
module Agda.Syntax.Translation.ConcreteToAbstract
    ( ToAbstract(..), localToAbstract
    , concreteToAbstract_
    , concreteToAbstract
    , NewModuleQName(..)
    , OldName(..)
    , TopLevel(..)
    , TopLevelInfo(..)
    , topLevelModuleName
    , AbstractRHS
    , NewModuleName, OldModuleName
    , NewName, OldQName
    , LeftHandSide, RightHandSide
    , PatName, APatName
    ) where

#if MIN_VERSION_base(4,11,0)
import Prelude hiding ( (<>), mapM, null )
#else
import Prelude hiding ( mapM, null )
#endif

import Control.Applicative
import Control.Arrow (second)
import Control.Monad.Reader hiding (mapM)

import Data.Foldable (Foldable, traverse_)
import Data.Traversable (mapM, traverse)
import Data.List ((\\), nub, foldl')
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import Data.Void

import Agda.Syntax.Concrete as C hiding (topLevelModuleName)
import Agda.Syntax.Concrete.Generic
import Agda.Syntax.Concrete.Operators
import Agda.Syntax.Concrete.Pattern
import Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pattern ( patternVars, checkPatternLinearity )
import Agda.Syntax.Abstract.Pretty
import qualified Agda.Syntax.Internal as I
import Agda.Syntax.Position
import Agda.Syntax.Literal
import Agda.Syntax.Common
import Agda.Syntax.Info
import Agda.Syntax.Concrete.Definitions as C
import Agda.Syntax.Fixity
import Agda.Syntax.Concrete.Fixity (DoWarn(..))
import Agda.Syntax.Notation
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Translation.AbstractToConcrete (ToConcrete)
import Agda.Syntax.DoNotation
import Agda.Syntax.IdiomBrackets

import Agda.TypeChecking.Monad.Base hiding (ModuleInfo, MetaInfo)
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Trace (traceCall, setCurrentRange)
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.MetaVars (registerInteractionPoint)
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Options
import Agda.TypeChecking.Monad.Env (insideDotPattern, isInsideDotPattern, getCurrentPath)
import Agda.TypeChecking.Rules.Builtin (isUntypedBuiltin, bindUntypedBuiltin, builtinKindOfName)

import Agda.TypeChecking.Patterns.Abstract (expandPatternSynonyms)
import Agda.TypeChecking.Pretty hiding (pretty, prettyA)
import Agda.TypeChecking.Warnings

import Agda.Interaction.FindFile (checkModuleName)
-- import Agda.Interaction.Imports  -- for type-checking in ghci
import {-# SOURCE #-} Agda.Interaction.Imports (scopeCheckImport)
import Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens
import Agda.Interaction.Options.Warnings

import Agda.Utils.AssocList (AssocList)
import qualified Agda.Utils.AssocList as AssocList
import Agda.Utils.Either
import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.FileName
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.NonemptyList
import Agda.Utils.Null
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Pretty (render, Pretty, pretty, prettyShow)
import Agda.Utils.Tuple
import Agda.Interaction.FindFile ( rootNameModule )

#include "undefined.h"
import Agda.Utils.Impossible
import Agda.ImpossibleTest (impossibleTest)

{--------------------------------------------------------------------------
    Exceptions
 --------------------------------------------------------------------------}

-- notAModuleExpr e = typeError $ NotAModuleExpr e

notAnExpression :: C.Expr -> ScopeM A.Expr
notAnExpression e = typeError $ NotAnExpression e

nothingAppliedToHiddenArg :: C.Expr -> ScopeM A.Expr
nothingAppliedToHiddenArg e = typeError $ NothingAppliedToHiddenArg e

nothingAppliedToInstanceArg :: C.Expr -> ScopeM A.Expr
nothingAppliedToInstanceArg e = typeError $ NothingAppliedToInstanceArg e

notAValidLetBinding :: NiceDeclaration -> ScopeM a
notAValidLetBinding d = typeError $ NotAValidLetBinding d

{--------------------------------------------------------------------------
    Helpers
 --------------------------------------------------------------------------}

annotateDecl :: ScopeM A.Declaration -> ScopeM A.Declaration
annotateDecl m = annotateDecls $ (:[]) <$> m

annotateDecls :: ScopeM [A.Declaration] -> ScopeM A.Declaration
annotateDecls m = do
  ds <- m
  s  <- getScope
  return $ ScopedDecl s ds

annotateExpr :: ScopeM A.Expr -> ScopeM A.Expr
annotateExpr m = do
  e <- m
  s <- getScope
  return $ ScopedExpr s e

-- | Make sure that there are no dot patterns (called on pattern synonyms).
noDotorEqPattern :: String -> A.Pattern' e -> ScopeM (A.Pattern' Void)
noDotorEqPattern err = dot
  where
    dot :: A.Pattern' e -> ScopeM (A.Pattern' Void)
    dot p = case p of
      A.VarP x               -> pure $ A.VarP x
      A.ConP i c args        -> A.ConP i c <$> (traverse $ traverse $ traverse dot) args
      A.ProjP i o d          -> pure $ A.ProjP i o d
      A.WildP i              -> pure $ A.WildP i
      A.AsP i x p            -> A.AsP i x <$> dot p
      A.DotP{}               -> genericError err
      A.EqualP{}             -> genericError err   -- Andrea: so we also disallow = patterns, reasonable?
      A.AbsurdP i            -> pure $ A.AbsurdP i
      A.LitP l               -> pure $ A.LitP l
      A.DefP i f args        -> A.DefP i f <$> (traverse $ traverse $ traverse dot) args
      A.PatternSynP i c args -> A.PatternSynP i c <$> (traverse $ traverse $ traverse dot) args
      A.RecP i fs            -> A.RecP i <$> (traverse $ traverse dot) fs
      A.WithP i p            -> A.WithP i <$> dot p

-- | Make sure that there are no dot patterns (WAS: called on pattern synonyms).
noDotPattern :: String -> A.Pattern' e -> ScopeM (A.Pattern' Void)
noDotPattern err = traverse $ const $ genericError err

newtype RecordConstructorType = RecordConstructorType [C.Declaration]

instance ToAbstract RecordConstructorType A.Expr where
  toAbstract (RecordConstructorType ds) = recordConstructorType ds

-- | Compute the type of the record constructor (with bogus target type)
recordConstructorType :: [C.Declaration] -> ScopeM A.Expr
recordConstructorType decls =
    -- Nicify all declarations since there might be fixity declarations after
    -- the the last field. Use NoWarn to silence fixity warnings. We'll get
    -- them again when scope checking the declarations to build the record
    -- module.
    niceDecls NoWarn decls $ buildType . takeFields
  where
    takeFields = List.dropWhileEnd notField

    notField NiceField{} = False
    notField _           = True

    buildType :: [C.NiceDeclaration] -> ScopeM A.Expr
    buildType ds = do
      tel <- mapM makeBinding ds  -- TODO: Telescope instead of Expr in abstract RecDef
      return $ A.Pi (ExprRange (getRange ds)) tel (A.Set exprNoRange 0)

    makeBinding :: C.NiceDeclaration -> ScopeM A.TypedBinding
    makeBinding d = do
      let failure = typeError $ NotValidBeforeField d
          r       = getRange d
          info    = ExprRange r
          mkLet d = A.TLet r <$> toAbstract (LetDef d)
      traceCall (SetRange r) $ case d of

        C.NiceField r pr ab inst x a -> do
          fx  <- getConcreteFixity x
          let bv = unnamed (C.mkBoundName x fx) <$ a
          tel <- toAbstract $ C.TBind r [bv] (unArg a)
          return tel

        -- Public open is allowed and will take effect when scope checking as
        -- proper declarations.
        C.NiceOpen r m dir -> do
          mkLet $ C.NiceOpen r m dir{ publicOpen = False }
        C.NiceModuleMacro r p x modapp open dir -> do
          mkLet $ C.NiceModuleMacro r p x modapp open dir{ publicOpen = False }

        -- Do some rudimentary matching here to get NotValidBeforeField instead
        -- of NotAValidLetDecl.
        C.NiceMutual _ _ _
          [ C.FunSig _ _ _ _instanc macro _info _ _ _
          , C.FunDef _ _ abstract _ _ _
             [ C.Clause _top _catchall (C.LHS _p [] []) (C.RHS _rhs) NoWhere [] ]
          ] | abstract /= AbstractDef && macro /= MacroDef -> do
          mkLet d

        C.NiceMutual{}        -> failure
        -- TODO: some of these cases might be __IMPOSSIBLE__
        C.Axiom{}             -> failure
        C.PrimitiveFunction{} -> failure
        C.NiceModule{}        -> failure
        C.NiceImport{}        -> failure
        C.NicePragma{}        -> failure
        C.NiceRecSig{}        -> failure
        C.NiceDataSig{}       -> failure
        C.NiceFunClause{}     -> failure
        C.FunSig{}            -> failure  -- Note: these are bundled with FunDef in NiceMutual
        C.FunDef{}            -> failure
        C.NiceDataDef{}       -> failure
        C.NiceRecDef{}        -> failure
        C.NicePatternSyn{}    -> failure
        C.NiceGeneralize{}    -> failure
        C.NiceUnquoteDecl{}   -> failure
        C.NiceUnquoteDef{}    -> failure

checkModuleApplication
  :: C.ModuleApplication
  -> ModuleName
  -> C.Name
  -> C.ImportDirective
  -> ScopeM (A.ModuleApplication, ScopeCopyInfo, A.ImportDirective)

checkModuleApplication (C.SectionApp _ tel e) m0 x dir' = do
  reportSDoc "scope.decl" 70 $ vcat $
    [ text $ "scope checking ModuleApplication " ++ prettyShow x
    ]

  -- For the following, set the current module to be m0.
  withCurrentModule m0 $ do
    -- Check that expression @e@ is of the form @m args@.
    (m, args) <- parseModuleApplication e
    -- Scope check the telescope (introduces bindings!).
    tel' <- toAbstract tel
    -- Scope check the old module name and the module args.
    m1    <- toAbstract $ OldModuleName m
    args' <- toAbstractCtx (ArgumentCtx PreferParen) args
    -- Drop constructors (OnlyQualified) if there are arguments. The record constructor
    -- isn't properly in the record module, so copying it will lead to badness.
    let noRecConstr | null args = id
                    | otherwise = removeOnlyQualified
    -- Copy the scope associated with m and take the parts actually imported.
    (adir, s) <- applyImportDirectiveM (C.QName x) dir' =<< getNamedScope m1
    (s', copyInfo) <- copyScope m m0 (noRecConstr s)
    -- Set the current scope to @s'@
    modifyCurrentScope $ const s'
    printScope "mod.inst" 20 "copied source module"
    reportSDoc "scope.mod.inst" 30 $ return $ pretty copyInfo
    let amodapp = A.SectionApp tel' m1 args'
    reportSDoc "scope.decl" 70 $ vcat $
      [ text $ "scope checked ModuleApplication " ++ prettyShow x
      ]
    reportSDoc "scope.decl" 70 $ vcat $
      [ nest 2 $ prettyA amodapp
      ]
    return (amodapp, copyInfo, adir)

checkModuleApplication (C.RecordModuleInstance _ recN) m0 x dir' =
  withCurrentModule m0 $ do
    m1 <- toAbstract $ OldModuleName recN
    s <- getNamedScope m1
    (adir, s) <- applyImportDirectiveM recN dir' s
    (s', copyInfo) <- copyScope recN m0 (removeOnlyQualified s)
    modifyCurrentScope $ const s'

    printScope "mod.inst" 20 "copied record module"
    return (A.RecordModuleInstance m1, copyInfo, adir)

-- | @checkModuleMacro mkApply range access concreteName modapp open dir@
--
--   Preserves local variables.

checkModuleMacro
  :: (Pretty c, ToConcrete a c)
  => (ModuleInfo
      -> ModuleName
      -> A.ModuleApplication
      -> ScopeCopyInfo
      -> A.ImportDirective
      -> a)
  -> OpenKind
  -> Range
  -> Access
  -> C.Name
  -> C.ModuleApplication
  -> OpenShortHand
  -> C.ImportDirective
  -> ScopeM [a]
checkModuleMacro apply kind r p x modapp open dir = do
    reportSDoc "scope.decl" 70 $ vcat $
      [ text $ "scope checking ModuleMacro " ++ prettyShow x
      ]
    notPublicWithoutOpen open dir

    m0 <- toAbstract (NewModuleName x)
    reportSDoc "scope.decl" 90 $ "NewModuleName: m0 =" <+> prettyA m0

    printScope "mod.inst" 20 "module macro"

    -- If we're opening a /named/ module, the import directive is
    -- applied to the "open", otherwise to the module itself. However,
    -- "public" is always applied to the "open".
    let (moduleDir, openDir) = case (open, isNoName x) of
          (DoOpen,   False) -> (defaultImportDir, dir)
          (DoOpen,   True)  -> ( dir { publicOpen = False }
                               , defaultImportDir { publicOpen = publicOpen dir }
                               )
          (DontOpen, _)     -> (dir, defaultImportDir)

    -- Restore the locals after module application has been checked.
    (modapp', copyInfo, adir') <- withLocalVars $ checkModuleApplication modapp m0 x moduleDir
    printScope "mod.inst.app" 20 "checkModuleMacro, after checkModuleApplication"

    reportSDoc "scope.decl" 90 $ "after mod app: trying to print m0 ..."
    reportSDoc "scope.decl" 90 $ "after mod app: m0 =" <+> prettyA m0

    bindModule p x m0
    reportSDoc "scope.decl" 90 $ "after bindMod: m0 =" <+> prettyA m0

    printScope "mod.inst.copy.after" 20 "after copying"

    -- Open the module if DoOpen.
    -- Andreas, 2014-09-02 openModule_ might shadow some locals!
    adir <- case open of
      DontOpen -> return adir'
      DoOpen   -> openModule_ kind (C.QName x) openDir
    printScope "mod.inst" 20 $ show open
    reportSDoc "scope.decl" 90 $ "after open   : m0 =" <+> prettyA m0

    stripNoNames
    printScope "mod.inst" 10 $ "after stripping"
    reportSDoc "scope.decl" 90 $ "after stripNo: m0 =" <+> prettyA m0

    let m      = m0 `withRangesOf` [x]
        adecls = [ apply info m modapp' copyInfo adir ]

    reportSDoc "scope.decl" 70 $ vcat $
      [ text $ "scope checked ModuleMacro " ++ prettyShow x
      ]
    reportSLn  "scope.decl" 90 $ "info    = " ++ show info
    reportSLn  "scope.decl" 90 $ "m       = " ++ prettyShow m
    reportSLn  "scope.decl" 90 $ "modapp' = " ++ show modapp'
    reportSDoc "scope.decl" 90 $ return $ pretty copyInfo
    reportSDoc "scope.decl" 70 $ vcat $
      map (nest 2 . prettyA) adecls
    return adecls
  where
    info = ModuleInfo
             { minfoRange  = r
             , minfoAsName = Nothing
             , minfoAsTo   = renamingRange dir
             , minfoOpenShort = Just open
             , minfoDirective = Just dir
             }

-- | The @public@ keyword must only be used together with @open@.

notPublicWithoutOpen :: OpenShortHand -> C.ImportDirective -> ScopeM ()
notPublicWithoutOpen DoOpen   dir = return ()
notPublicWithoutOpen DontOpen dir = when (publicOpen dir) $ genericError
    "The public keyword must only be used together with the open keyword"

-- | Computes the range of all the \"to\" keywords used in a renaming
-- directive.

renamingRange :: C.ImportDirective -> Range
renamingRange = getRange . map renToRange . impRenaming

-- | Scope check a 'NiceOpen'.
checkOpen
  :: Range -> C.QName -> C.ImportDirective                -- ^ Arguments of 'NiceOpen'
  -> ScopeM (ModuleInfo, A.ModuleName, A.ImportDirective) -- ^ Arguments of 'A.Open'
checkOpen r x dir = do
  reportSDoc "scope.decl" 70 $ do
    cm <- getCurrentModule
    vcat $
      [ text   "scope checking NiceOpen " <> return (pretty x)
      , text   "  getCurrentModule       = " <> prettyA cm
      , text $ "  getCurrentModule (raw) = " ++ show cm
      , text $ "  C.ImportDirective      = " ++ prettyShow dir
      ]
  -- Andreas, 2017-01-01, issue #2377: warn about useless `public`
  when (publicOpen dir) $ do
    whenM ((A.noModuleName ==) <$> getCurrentModule) $ do
      warning $ UselessPublic

  m <- toAbstract (OldModuleName x)
  printScope "open" 20 $ "opening " ++ prettyShow x
  adir <- openModule_ TopOpenModule x dir
  printScope "open" 20 $ "result:"
  let minfo = ModuleInfo
        { minfoRange     = r
        , minfoAsName    = Nothing
        , minfoAsTo      = renamingRange dir
        , minfoOpenShort = Nothing
        , minfoDirective = Just dir
        }
  let adecls = [A.Open minfo m adir]
  reportSDoc "scope.decl" 70 $ vcat $
    [ text $ "scope checked NiceOpen " ++ prettyShow x
    ] ++ map (nest 2 . prettyA) adecls
  return (minfo, m, adir)

{--------------------------------------------------------------------------
    Translation
 --------------------------------------------------------------------------}

concreteToAbstract_ :: ToAbstract c a => c -> ScopeM a
concreteToAbstract_ = toAbstract

concreteToAbstract :: ToAbstract c a => ScopeInfo -> c -> ScopeM a
concreteToAbstract scope x = withScope_ scope (toAbstract x)

-- | Things that can be translated to abstract syntax are instances of this
--   class.
class ToAbstract concrete abstract | concrete -> abstract where
    toAbstract :: concrete -> ScopeM abstract

-- | This function should be used instead of 'toAbstract' for things that need
--   to keep track of precedences to make sure that we don't forget about it.
toAbstractCtx :: ToAbstract concrete abstract =>
                 Precedence -> concrete -> ScopeM abstract
toAbstractCtx ctx c = withContextPrecedence ctx $ toAbstract c

toAbstractTopCtx :: ToAbstract c a => c -> ScopeM a
toAbstractTopCtx = toAbstractCtx TopCtx

toAbstractHiding :: (LensHiding h, ToAbstract c a) => h -> c -> ScopeM a
toAbstractHiding h | visible h = toAbstract -- don't change precedence if visible
toAbstractHiding _             = toAbstractCtx TopCtx

setContextCPS :: Precedence -> (a -> ScopeM b) ->
                 ((a -> ScopeM b) -> ScopeM b) -> ScopeM b
setContextCPS p ret f = do
  old <- scopePrecedence <$> getScope
  withContextPrecedence p $ f $ \ x -> setContextPrecedence old >> ret x

localToAbstractCtx :: ToAbstract concrete abstract =>
                     Precedence -> concrete -> (abstract -> ScopeM a) -> ScopeM a
localToAbstractCtx ctx c ret = setContextCPS ctx ret (localToAbstract c)

-- | This operation does not affect the scope, i.e. the original scope
--   is restored upon completion.
localToAbstract :: ToAbstract c a => c -> (a -> ScopeM b) -> ScopeM b
localToAbstract x ret = fst <$> localToAbstract' x ret

-- | Like 'localToAbstract' but returns the scope after the completion of the
--   second argument.
localToAbstract' :: ToAbstract c a => c -> (a -> ScopeM b) -> ScopeM (b, ScopeInfo)
localToAbstract' x ret = do
  scope <- getScope
  withScope scope $ ret =<< toAbstract x

instance (ToAbstract c1 a1, ToAbstract c2 a2) => ToAbstract (c1,c2) (a1,a2) where
  toAbstract (x,y) = (,) <$> toAbstract x <*> toAbstract y

instance (ToAbstract c1 a1, ToAbstract c2 a2, ToAbstract c3 a3) =>
         ToAbstract (c1,c2,c3) (a1,a2,a3) where
    toAbstract (x,y,z) = flatten <$> toAbstract (x,(y,z))
        where
            flatten (x,(y,z)) = (x,y,z)

instance {-# OVERLAPPABLE #-} ToAbstract c a => ToAbstract [c] [a] where
  toAbstract = mapM toAbstract

instance (ToAbstract c1 a1, ToAbstract c2 a2) =>
         ToAbstract (Either c1 c2) (Either a1 a2) where
    toAbstract = traverseEither toAbstract toAbstract

instance ToAbstract c a => ToAbstract (Maybe c) (Maybe a) where
  toAbstract = traverse toAbstract

-- Names ------------------------------------------------------------------

data NewName a = NewName
  { newBinder   :: Binder -- what kind of binder?
  , newName     :: a
  }

data OldQName     = OldQName C.QName (Maybe (Set A.Name))
  -- ^ If a set is given, then the first name must correspond to one
  -- of the names in the set.
newtype OldName a = OldName a

-- | Wrapper to resolve a name to a 'ResolvedName' (rather than an 'A.Expr').
data ResolveQName = ResolveQName C.QName

data PatName      = PatName C.QName (Maybe (Set A.Name))
  -- ^ If a set is given, then the first name must correspond to one
  -- of the names in the set.

instance ToAbstract (NewName C.Name) A.Name where
  toAbstract (NewName b x) = do
    y <- freshAbstractName_ x
    bindVariable b x y
    return y

instance ToAbstract (NewName C.BoundName) A.BindName where
  toAbstract (NewName b BName{ boundName = x, bnameFixity = fx }) = do
    y <- freshAbstractName fx x
    bindVariable b x y
    return $ A.BindName y

instance ToAbstract OldQName A.Expr where
  toAbstract (OldQName x ns) = do
    qx <- resolveName' allKindsOfNames ns x
    reportSLn "scope.name" 10 $ "resolved " ++ prettyShow x ++ ": " ++ prettyShow qx
    case qx of
      VarName x' _         -> return $ A.Var x'
      DefinedName _ d      -> do
        -- In case we find a defined name, we start by checking whether there's
        -- a warning attached to it
        reportSDoc "scope.warning" 50 $ text $ "Checking usage of " ++ prettyShow d
        mstr <- Map.lookup (anameName d) <$> getUserWarnings
        forM_ mstr (warning . UserWarning)
        -- then we take note of generalized names used
        case anameKind d of
          GeneralizeName -> do
            gvs <- useTC stGeneralizedVars
            case gvs of   -- Subtle: Use (left-biased) union instead of insert to keep the old name if
                          -- already present. This way we can sort by source location when generalizing
                          -- (Issue 3354).
                Just s -> stGeneralizedVars `setTCLens` Just (s `Set.union` Set.singleton (anameName d))
                Nothing -> typeError $ GeneralizeNotSupportedHere $ anameName d
          DisallowedGeneralizeName -> do
            typeError . GenericDocError =<<
              text "Cannot use generalized variable from let-opened module:" <+> prettyTCM (anameName d)
          _ -> return ()
        -- and then we return the name
        return $ nameExpr d
      FieldName     ds     -> return $ A.Proj ProjPrefix $ AmbQ (fmap anameName ds)
      ConstructorName ds   -> return $ A.Con $ AmbQ (fmap anameName ds)
      UnknownName          -> notInScope x
      PatternSynResName ds -> return $ A.PatternSyn $ AmbQ (fmap anameName ds)

instance ToAbstract ResolveQName ResolvedName where
  toAbstract (ResolveQName x) = resolveName x >>= \case
    UnknownName -> notInScope x
    q -> return q

data APatName = VarPatName A.Name
              | ConPatName (NonemptyList AbstractName)
              | PatternSynPatName (NonemptyList AbstractName)

instance ToAbstract PatName APatName where
  toAbstract (PatName x ns) = do
    reportSLn "scope.pat" 10 $ "checking pattern name: " ++ prettyShow x
    rx <- resolveName' [ConName, PatternSynName] ns x
          -- Andreas, 2013-03-21 ignore conflicting names which cannot
          -- be meant since we are in a pattern
    case (rx, x) of
      (VarName y _,     C.QName x)                          -> bindPatVar x
      (FieldName d,     C.QName x)                          -> bindPatVar x
      (DefinedName _ d, C.QName x) | DefName == anameKind d -> bindPatVar x
      (UnknownName,     C.QName x)                          -> bindPatVar x
      (ConstructorName ds, _)                               -> patCon ds
      (PatternSynResName d, _)                              -> patSyn d
      _ -> genericError $ "Cannot pattern match on non-constructor " ++ prettyShow x
    where
      bindPatVar = VarPatName <.> bindPatternVariable
      patCon ds = do
        reportSLn "scope.pat" 10 $ "it was a con: " ++ prettyShow (fmap anameName ds)
        return $ ConPatName ds
      patSyn ds = do
        reportSLn "scope.pat" 10 $ "it was a pat syn: " ++ prettyShow (fmap anameName ds)
        return $ PatternSynPatName ds

-- | Translate and possibly bind a pattern variable
--   (which could have been bound before due to non-linearity).
bindPatternVariable :: C.Name -> ScopeM A.Name
bindPatternVariable x = do
  reportSLn "scope.pat" 10 $ "it was a var: " ++ prettyShow x
  y <- (AssocList.lookup x <$> getVarsToBind) >>= \case
    Just (LocalVar y _ _) -> return $ setRange (getRange x) y
    Nothing -> freshAbstractName_ x
  addVarToBind x $ LocalVar y PatternBound []
  return y

class ToQName a where
  toQName :: a -> C.QName

instance ToQName C.Name  where toQName = C.QName
instance ToQName C.QName where toQName = id

-- Should be a defined name.
instance (Show a, ToQName a) => ToAbstract (OldName a) A.QName where
  toAbstract (OldName x) = do
    rx <- resolveName (toQName x)
    case rx of
      DefinedName _ d      -> return $ anameName d
      -- We can get the cases below for DISPLAY pragmas
      ConstructorName ds   -> return $ anameName (headNe ds)   -- We'll throw out this one, so it doesn't matter which one we pick
      FieldName ds         -> return $ anameName (headNe ds)
      PatternSynResName ds -> return $ anameName (headNe ds)
      VarName x _          -> genericError $ "Not a defined name: " ++ prettyShow x
      UnknownName          -> notInScope (toQName x)

newtype NewModuleName      = NewModuleName      C.Name
newtype NewModuleQName     = NewModuleQName     C.QName
newtype OldModuleName      = OldModuleName      C.QName

freshQModule :: A.ModuleName -> C.Name -> ScopeM A.ModuleName
freshQModule m x = A.qualifyM m . mnameFromList . (:[]) <$> freshAbstractName_ x

checkForModuleClash :: C.Name -> ScopeM ()
checkForModuleClash x = do
  ms <- scopeLookup (C.QName x) <$> getScope
  unless (null ms) $ do
    reportSLn "scope.clash" 20 $ "clashing modules ms = " ++ prettyShow ms
    reportSLn "scope.clash" 60 $ "clashing modules ms = " ++ show ms
    setCurrentRange x $
      typeError $ ShadowedModule x $
                map ((`withRangeOf` x) . amodName) ms

instance ToAbstract NewModuleName A.ModuleName where
  toAbstract (NewModuleName x) = do
    checkForModuleClash x
    m <- getCurrentModule
    y <- freshQModule m x
    createModule Nothing y
    return y

instance ToAbstract NewModuleQName A.ModuleName where
  toAbstract (NewModuleQName m) = toAbs noModuleName m
    where
      toAbs m (C.QName x)  = do
        y <- freshQModule m x
        createModule Nothing y
        return y
      toAbs m (C.Qual x q) = do
        m' <- freshQModule m x
        toAbs m' q

instance ToAbstract OldModuleName A.ModuleName where
  toAbstract (OldModuleName q) = setCurrentRange q $ do
    amodName <$> resolveModule q

-- Expressions ------------------------------------------------------------

-- | Peel off 'C.HiddenArg' and represent it as an 'NamedArg'.
mkNamedArg :: C.Expr -> NamedArg C.Expr
mkNamedArg (C.HiddenArg   _ e) = Arg (hide         defaultArgInfo) e
mkNamedArg (C.InstanceArg _ e) = Arg (makeInstance defaultArgInfo) e
mkNamedArg e                   = Arg defaultArgInfo $ unnamed e

-- | Peel off 'C.HiddenArg' and represent it as an 'Arg', throwing away any name.
mkArg' :: ArgInfo -> C.Expr -> Arg C.Expr
mkArg' info (C.HiddenArg   _ e) = Arg (hide         info) $ namedThing e
mkArg' info (C.InstanceArg _ e) = Arg (makeInstance info) $ namedThing e
mkArg' info e                   = Arg (setHiding NotHidden info) e

-- | By default, arguments are @Relevant@.
mkArg :: C.Expr -> Arg C.Expr
mkArg e = mkArg' defaultArgInfo e

inferParenPreference :: C.Expr -> ParenPreference
inferParenPreference C.Paren{} = PreferParen
inferParenPreference _         = PreferParenless

-- | Parse a possibly dotted C.Expr as A.Expr.  Bool = True if dotted.
toAbstractDot :: Precedence -> C.Expr -> ScopeM (A.Expr, Bool)
toAbstractDot prec e = do
    reportSLn "scope.irrelevance" 100 $ "toAbstractDot: " ++ (render $ pretty e)
    traceCall (ScopeCheckExpr e) $ case e of

      C.Dot _ e -> do
        e <- toAbstractCtx prec e
        return (e, True)

      C.RawApp r es -> do
        e <- parseApplication es
        toAbstractDot prec e

      C.Paren _ e -> toAbstractDot TopCtx e

      e -> do
        e <- toAbstractCtx prec e
        return (e, False)

-- | Translate concrete expression under at least one binder into nested
--   lambda abstraction in abstract syntax.
toAbstractLam :: Range -> [C.LamBinding] -> C.Expr -> Precedence -> ScopeM A.Expr
toAbstractLam r bs e ctx = do
  -- Translate the binders
  localToAbstract (map (C.DomainFull . makeDomainFull) bs) $ \ bs -> do
    -- Translate the body
    e <- toAbstractCtx ctx e
    -- We have at least one binder.  Get first @b@ and rest @bs@.
    caseList bs __IMPOSSIBLE__ $ \ b bs -> do
      return $ A.Lam (ExprRange r) b $ foldr mkLam e bs
  where
    mkLam b e = A.Lam (ExprRange $ fuseRange b e) b e

-- | Scope check extended lambda expression.
scopeCheckExtendedLam :: Range -> [C.LamClause] -> ScopeM A.Expr
scopeCheckExtendedLam r cs = do
  whenM isInsideDotPattern $
    genericError "Extended lambdas are not allowed in dot patterns"

  -- Find an unused name for the extended lambda definition.
  cname <- nextlamname r 0 extendedLambdaName
  name  <- freshAbstractName_ cname
  reportSLn "scope.extendedLambda" 10 $ "new extended lambda name: " ++ prettyShow name
  verboseS "scope.extendedLambda" 60 $ do
    forM_ cs $ \ c -> do
      reportSLn "scope.extendedLambda" 60 $ "extended lambda lhs: " ++ show (C.lamLHS c)
  qname <- qualifyName_ name
  bindName (PrivateAccess Inserted) DefName cname qname

  -- Compose a function definition and scope check it.
  a <- aModeToDef <$> asksTC envAbstractMode
  let
    insertApp :: C.Pattern -> ScopeM C.Pattern
    insertApp (C.RawAppP r es) = return $ C.RawAppP r $ IdentP (C.QName cname) : es
    insertApp (C.AppP p1 p2)   = return $ (IdentP (C.QName cname) `C.AppP` defaultNamedArg p1) `C.AppP` p2  -- Case occurs in issue #2785
    insertApp p = return $ C.RawAppP r $ IdentP (C.QName cname) : [p] -- Issue #2807: C.ParenP also possible
      where r = getRange p
      -- Andreas, 2017-10-17 issue #2807: do not raise IMPOSSSIBLE here
      -- since we are actually not sure what is possible and what not.

    -- insertApp (C.IdentP q    ) = return $ C.RawAppP r $ IdentP (C.QName cname) : [C.IdentP q]
    --   where r = getRange q
    -- insertApp p = do
    --   reportSLn "impossible" 10 $ "scopeCheckExtendedLam: unexpected pattern: " ++
    --     case p of
    --       C.QuoteP{}    -> "QuoteP"
    --       C.OpAppP{}    -> "OpAppP"
    --       C.HiddenP{}   -> "HiddenP"
    --       C.InstanceP{} -> "InstanceP"
    --       C.ParenP{}    -> "ParenP"
    --       C.WildP{}     -> "WildP"
    --       C.AbsurdP{}   -> "AbsurdP"
    --       C.AsP{}       -> "AsP"
    --       C.DotP{}      -> "DotP"
    --       C.LitP{}      -> "LitP"
    --       C.RecP{}      -> "RecP"
    --       _ -> __IMPOSSIBLE__
    --   __IMPOSSIBLE__

  d <- C.FunDef r [] a NotInstanceDef __IMPOSSIBLE__ cname <$> do
          forM cs $ \ (LamClause lhs rhs wh ca) -> do -- wh == NoWhere, see parser for more info
            lhs' <- mapLhsOriginalPatternM insertApp lhs
            return $ C.Clause cname ca lhs' rhs wh []
  scdef <- toAbstract d

  -- Create the abstract syntax for the extended lambda.
  case scdef of
    A.ScopedDecl si [A.FunDef di qname' NotDelayed cs] -> do
      setScope si  -- This turns into an A.ScopedExpr si $ A.ExtendedLam...
      return $ A.ExtendedLam (ExprRange r) di qname' cs
    _ -> __IMPOSSIBLE__

  where
    -- Get a concrete name that is not yet in scope.
    nextlamname :: Range -> Int -> String -> ScopeM C.Name
    nextlamname r i s = do
      let cname = C.Name r C.NotInScope [Id $ stringToRawName $ s ++ show i]
      rn <- resolveName $ C.QName cname
      case rn of
        UnknownName -> return cname
        _           -> nextlamname r (i+1) s

instance ToAbstract C.Expr A.Expr where
  toAbstract e =
    traceCall (ScopeCheckExpr e) $ annotateExpr $ case e of

  -- Names
      Ident x -> toAbstract (OldQName x Nothing)

  -- Literals
      C.Lit l ->
        case l of
          LitNat r n -> do
            let builtin | n < 0     = Just <$> primFromNeg    -- negative literals are only allowed if FROMNEG is defined
                        | otherwise = ensureInScope =<< getBuiltin' builtinFromNat
                l'   = LitNat r (abs n)
                info = defaultAppInfo r
            conv <- builtin
            case conv of
              Just (I.Def q _) -> return $ A.App info (A.Def q) $ defaultNamedArg (A.Lit l')
              _                -> return $ A.Lit l

          LitString r s -> do
            conv <- ensureInScope =<< getBuiltin' builtinFromString
            let info = defaultAppInfo r
            case conv of
              Just (I.Def q _) -> return $ A.App info (A.Def q) $ defaultNamedArg (A.Lit l)
              _                -> return $ A.Lit l

          _ -> return $ A.Lit l
        where
          ensureInScope :: Maybe I.Term -> ScopeM (Maybe I.Term)
          ensureInScope v@(Just (I.Def q _)) = ifM (isNameInScope q <$> getScope) (return v) (return Nothing)
          ensureInScope _ = return Nothing

  -- Meta variables
      C.QuestionMark r n -> do
        scope <- getScope
        -- Andreas, 2014-04-06 create interaction point.
        ii <- registerInteractionPoint True r n
        let info = MetaInfo
             { metaRange  = r
             , metaScope  = scope
             , metaNumber = Nothing
             , metaNameSuggestion = ""
             }
        return $ A.QuestionMark info ii
      C.Underscore r n -> do
        scope <- getScope
        return $ A.Underscore $ MetaInfo
                    { metaRange  = r
                    , metaScope  = scope
                    , metaNumber = maybe Nothing __IMPOSSIBLE__ n
                    , metaNameSuggestion = fromMaybe "" n
                    }

  -- Raw application
      C.RawApp r es -> do
        e <- parseApplication es
        toAbstract e

  -- Application
      C.App r e1 e2 -> do
        let parenPref = inferParenPreference (namedArg e2)
            info = (defaultAppInfo r) { appOrigin = UserWritten, appParens = parenPref }
        e1 <- toAbstractCtx FunctionCtx e1
        e2 <- toAbstractCtx (ArgumentCtx parenPref) e2
        return $ A.App info e1 e2

  -- Operator application
      C.OpApp r op ns es -> toAbstractOpApp op ns es

  -- With application
      C.WithApp r e es -> do
        e  <- toAbstractCtx WithFunCtx e
        es <- mapM (toAbstractCtx WithArgCtx) es
        return $ A.WithApp (ExprRange r) e es

  -- Misplaced hidden argument
      C.HiddenArg _ _ -> nothingAppliedToHiddenArg e
      C.InstanceArg _ _ -> nothingAppliedToInstanceArg e

  -- Lambda
      C.AbsurdLam r h -> return $ A.AbsurdLam (ExprRange r) h

      C.Lam r bs e -> toAbstractLam r bs e TopCtx

  -- Extended Lambda
      C.ExtendedLam r cs -> scopeCheckExtendedLam r cs

  -- Relevant and irrelevant non-dependent function type
      C.Fun r (Arg info1 e1) e2 -> do
        Arg info (e0, dotted) <- traverse (toAbstractDot FunctionSpaceDomainCtx) $ mkArg' info1 e1
        let e1 = Arg ((if dotted then setRelevance Irrelevant else id) info) e0
        e2 <- toAbstractCtx TopCtx e2
        return $ A.Fun (ExprRange r) e1 e2

  -- Dependent function type
      e0@(C.Pi tel e) ->
        localToAbstract tel $ \tel -> do
        e    <- toAbstractCtx TopCtx e
        let info = ExprRange (getRange e0)
        return $ A.Pi info tel e

  -- Sorts
      C.Set _    -> return $ A.Set (ExprRange $ getRange e) 0
      C.SetN _ n -> return $ A.Set (ExprRange $ getRange e) n
      C.Prop _   -> return $ A.Prop (ExprRange $ getRange e) 0
      C.PropN _ n -> return $ A.Prop (ExprRange $ getRange e) n

  -- Let
      e0@(C.Let _ ds (Just e)) ->
        ifM isInsideDotPattern (genericError $ "Let-expressions are not allowed in dot patterns") $
        localToAbstract (LetDefs ds) $ \ds' -> do
          e <- toAbstractCtx TopCtx e
          let info = ExprRange (getRange e0)
          return $ A.Let info ds' e
      C.Let _ _ Nothing -> genericError "Missing body in let-expression"

  -- Record construction
      C.Rec r fs  -> do
        fs' <- toAbstractCtx TopCtx fs
        let ds'  = [ d | Right (_, ds) <- fs', d <- ds ]
            fs'' = map (mapRight fst) fs'
            i    = ExprRange r
        return $ A.mkLet i ds' (A.Rec i fs'')

  -- Record update
      C.RecUpdate r e fs -> do
        A.RecUpdate (ExprRange r) <$> toAbstract e <*> toAbstractCtx TopCtx fs

  -- Parenthesis
      C.Paren _ e -> toAbstractCtx TopCtx e

  -- Idiom brackets
      C.IdiomBrackets r e ->
        toAbstractCtx TopCtx =<< parseIdiomBrackets r e

  -- Do notation
      C.DoBlock r ss ->
        toAbstractCtx TopCtx =<< desugarDoNotation r ss

  -- Post-fix projections
      C.Dot r e  -> A.Dot (ExprRange r) <$> toAbstract e

  -- Pattern things
      C.As _ _ _ -> notAnExpression e
      C.Absurd _ -> notAnExpression e

  -- Impossible things
      C.ETel _  -> __IMPOSSIBLE__
      C.Equal{} -> genericError "Parse error: unexpected '='"
      C.Ellipsis _ -> genericError "Parse error: unexpected '...'"

  -- Quoting
      C.QuoteGoal _ x e -> do
        x' <- toAbstract (NewName LetBound x)
        e' <- toAbstract e
        return $ A.QuoteGoal (ExprRange $ getRange e) x' e'
      C.QuoteContext r -> return $ A.QuoteContext (ExprRange r)
      C.Quote r -> return $ A.Quote (ExprRange r)
      C.QuoteTerm r -> return $ A.QuoteTerm (ExprRange r)
      C.Unquote r -> return $ A.Unquote (ExprRange r)

      C.Tactic r e es -> do
        let AppView e' args = appView e
        e' : es <- toAbstract (e' : es)
        args    <- toAbstract args
        return $ A.Tactic (ExprRange r) e' args (map defaultNamedArg es)

  -- DontCare
      C.DontCare e -> A.DontCare <$> toAbstract e

  -- forall-generalize
      C.Generalized e -> do
        (s, e) <- collectGeneralizables $ toAbstract e
        pure $ A.generalized s e

instance ToAbstract C.ModuleAssignment (A.ModuleName, [A.LetBinding]) where
  toAbstract (C.ModuleAssignment m es i)
    | null es && isDefaultImportDir i = (, []) <$> toAbstract (OldModuleName m)
    | otherwise = do
        x <- C.NoName (getRange m) <$> fresh
        r <- checkModuleMacro LetApply LetOpenModule (getRange (m, es, i)) PublicAccess x
                          (C.SectionApp (getRange (m , es)) [] (RawApp (fuseRange m es) (Ident m : es)))
                          DontOpen i
        case r of
          (LetApply _ m' _ _ _ : _) -> return (m', r)
          _ -> __IMPOSSIBLE__

instance ToAbstract c a => ToAbstract (FieldAssignment' c) (FieldAssignment' a) where
  toAbstract = traverse toAbstract

instance ToAbstract C.LamBinding A.LamBinding where
  toAbstract (C.DomainFree x)  = A.DomainFree <$> toAbstract ((fmap . fmap) (NewName LambdaBound) x)
  toAbstract (C.DomainFull tb) = A.DomainFull <$> toAbstract tb

makeDomainFull :: C.LamBinding -> C.TypedBinding
makeDomainFull (C.DomainFull b) = b
makeDomainFull (C.DomainFree x) = C.TBind r [x] $ C.Underscore r Nothing
  where r = getRange x

instance ToAbstract C.TypedBinding A.TypedBinding where
  toAbstract (C.TBind r xs t) = do
    t' <- toAbstractCtx TopCtx t
    xs' <- toAbstract $ (map . fmap . fmap) (NewName LambdaBound) xs
    return $ A.TBind r xs' t'
  toAbstract (C.TLet r ds) = A.TLet r <$> toAbstract (LetDefs ds)

-- | Scope check a module (top level function).
--
scopeCheckNiceModule
  :: Range
  -> Access
  -> C.Name
  -> C.Telescope
  -> ScopeM [A.Declaration]
  -> ScopeM [A.Declaration]
scopeCheckNiceModule r p name tel checkDs
  | telHasOpenStmsOrModuleMacros tel = do
      -- Andreas, 2013-12-10:
      -- If the module telescope contains open statements
      -- or module macros (Issue 1299),
      -- add an extra anonymous module around the current one.
      -- Otherwise, the open statements would create
      -- identifiers in the parent scope of the current module.
      -- But open statements in the module telescope should
      -- only affect the current module!
      scopeCheckNiceModule noRange p noName_ [] $
        scopeCheckNiceModule_

  | otherwise = do
        scopeCheckNiceModule_
  where
    -- The actual workhorse:
    scopeCheckNiceModule_ = do

      -- Check whether we are dealing with an anonymous module.
      -- This corresponds to a Coq/LEGO section.
      (name, p', open) <- do
        if isNoName name then do
          (i :: NameId) <- fresh
          return (C.NoName (getRange name) i, PrivateAccess Inserted, True)
         else return (name, p, False)

      -- Check and bind the module, using the supplied check for its contents.
      aname <- toAbstract (NewModuleName name)
      ds <- snd <$> do
        scopeCheckModule r (C.QName name) aname tel checkDs
      bindModule p' name aname

      -- If the module was anonymous open it public
      -- unless it's private, in which case we just open it (#2099)
      when open $
       void $ -- We can discard the returned default A.ImportDirective.
        openModule_ TopOpenModule (C.QName name) $
          defaultImportDir { publicOpen = p == PublicAccess }
      return ds

-- | Check whether a telescope has open declarations or module macros.
telHasOpenStmsOrModuleMacros :: C.Telescope -> Bool
telHasOpenStmsOrModuleMacros = any yesBind
  where
    yesBind C.TBind{}     = False
    yesBind (C.TLet _ ds) = any yes ds
    yes C.ModuleMacro{}   = True
    yes C.Open{}          = True
    yes C.Import{}        = True -- not __IMPOSSIBLE__, see Issue #1718
      -- However, it does not matter what we return here, as this will
      -- become an error later: "Not a valid let-declaration".
      -- (Andreas, 2015-11-17)
    yes (C.Mutual   _ ds) = any yes ds
    yes (C.Abstract _ ds) = any yes ds
    yes (C.Private _ _ ds) = any yes ds
    yes _                 = False

{- UNUSED
telHasLetStms :: C.Telescope -> Bool
telHasLetStms = any isLetBind
  where
    isLetBind C.TBind{} = False
    isLetBind C.TLet{}  = True
-}

-- | We for now disallow let-bindings in @data@ and @record@ telescopes.
--   This due "nested datatypes"; there is no easy interpretation of
--   @
--      data D (A : Set) (open M A) (b : B) : Set where
--        c : D (A × A) b → D A b
--   @
--   where @B@ is brought in scope by @open M A@.

class EnsureNoLetStms a where
  ensureNoLetStms :: a -> ScopeM ()

{- From ghc 7.2, there is LANGUAGE DefaultSignatures
  default ensureNoLetStms :: Foldable t => t a -> ScopeM ()
  ensureNoLetStms = traverse_ ensureNoLetStms
-}

instance EnsureNoLetStms C.TypedBinding where
  ensureNoLetStms tb =
    case tb of
      C.TLet{}  -> typeError $ IllegalLetInTelescope tb
      C.TBind{} -> return ()

instance EnsureNoLetStms a => EnsureNoLetStms (LamBinding' a) where
  ensureNoLetStms = traverse_ ensureNoLetStms

instance EnsureNoLetStms a => EnsureNoLetStms [a] where
  ensureNoLetStms = traverse_ ensureNoLetStms


-- | Returns the scope inside the checked module.
scopeCheckModule
  :: Range
  -> C.QName                 -- ^ The concrete name of the module.
  -> A.ModuleName            -- ^ The abstract name of the module.
  -> C.Telescope             -- ^ The module telescope.
  -> ScopeM [A.Declaration]  -- ^ The code for checking the module contents.
  -> ScopeM (ScopeInfo, [A.Declaration])
scopeCheckModule r x qm tel checkDs = do
  printScope "module" 20 $ "checking module " ++ prettyShow x
  -- Andreas, 2013-12-10: Telescope does not live in the new module
  -- but its parent, so check it before entering the new module.
  -- This is important for Nicolas Pouillard's open parametrized modules
  -- statements inside telescopes.
  res <- withLocalVars $ do
    tel <- toAbstract (GenTel tel)
    withCurrentModule qm $ do
      -- pushScope m
      -- qm <- getCurrentModule
      printScope "module" 20 $ "inside module " ++ prettyShow x
      ds    <- checkDs
      scope <- getScope
      return (scope, [ A.Section info (qm `withRangesOfQ` x) tel ds ])

  -- Binding is done by the caller
  printScope "module" 20 $ "after module " ++ prettyShow x
  return res
  where
    info = ModuleInfo r noRange Nothing Nothing Nothing

-- | Temporary data type to scope check a file.
data TopLevel a = TopLevel
  { topLevelPath           :: AbsolutePath
    -- ^ The file path from which we loaded this module.
  , topLevelExpectedName   :: C.TopLevelModuleName
    -- ^ The expected module name
    --   (coming from the import statement that triggered scope checking this file).
  , topLevelTheThing       :: a
    -- ^ The file content.
  }

data TopLevelInfo = TopLevelInfo
        { topLevelDecls :: [A.Declaration]
        , topLevelScope :: ScopeInfo  -- ^ as seen from inside the module
        }

-- | The top-level module name.

topLevelModuleName :: TopLevelInfo -> A.ModuleName
topLevelModuleName = scopeCurrent . topLevelScope

-- | Top-level declarations are always
--   @
--     (import|open)*         -- a bunch of possibly opened imports
--     module ThisModule ...  -- the top-level module of this file
--   @
instance ToAbstract (TopLevel [C.Declaration]) TopLevelInfo where
    toAbstract (TopLevel file expectedMName ds) =
      -- A file is a bunch of preliminary decls (imports etc.)
      -- plus a single module decl.
      case C.spanAllowedBeforeModule ds of

        -- If there are declarations after the top-level module
        -- we have to report a parse error here.
        (_, C.Module{} : d : _) -> traceCall (SetRange $ getRange d) $
          genericError $ "No declarations allowed after top-level module."

        -- Otherwise, proceed.
        (outsideDecls, [ C.Module r m0 tel insideDecls ]) -> do
          -- If the module name is _ compute the name from the file path
          m <- if isNoName m0
                then do
                  -- Andreas, 2017-07-28, issue #1077
                  -- Check if the insideDecls end in a single module which has the same
                  -- name as the file.  In this case, it is highly likely that the user
                  -- put some non-allowed declarations before the top-level module in error.
                  -- Andreas, 2017-10-19, issue #2808
                  -- Widen this check to:
                  -- If the first module of the insideDecls has the same name as the file,
                  -- report an error.
                  case flip span insideDecls $ \case { C.Module{} -> False; _ -> True } of
                    (ds0, (C.Module _ m1 _ _ : _))
                       | C.toTopLevelModuleName m1 == expectedMName
                         -- If the anonymous module comes from the user,
                         -- the range cannot be the beginningOfFile.
                         -- That is the range if the parser inserted the anon. module.
                       , r == beginningOfFile (getRange insideDecls) -> do

                         traceCall (SetRange $ getRange ds0) $ genericError
                           "Illegal declaration(s) before top-level module"

                    -- Otherwise, reconstruct the top-level module name
                    _ -> return $ C.QName $ C.Name (getRange m0) C.InScope
                           [Id $ stringToRawName $ rootNameModule file]
                -- Andreas, 2017-05-17, issue #2574, keep name as jump target!
                -- Andreas, 2016-07-12, ALTERNATIVE:
                -- -- We assign an anonymous file module the name expected from
                -- -- its import.  For flat file structures, this is the same.
                -- -- For hierarchical file structures, this reverses the behavior:
                -- -- Loading the file by itself will fail, but it can be imported.
                -- -- The previous behavior is: it can be loaded by itself, but not
                -- -- be imported
                -- then return $ C.fromTopLevelModuleName expectedMName
                else do
                -- Andreas, 2014-03-28  Issue 1078
                -- We need to check the module name against the file name here.
                -- Otherwise one could sneak in a lie and confuse the scope
                -- checker.
                  checkModuleName (C.toTopLevelModuleName m0) file $ Just expectedMName
                  return m0
          setTopLevelModule m
          am           <- toAbstract (NewModuleQName m)
          -- Scope check the declarations outside
          outsideDecls <- toAbstract outsideDecls
          (insideScope, insideDecls) <- scopeCheckModule r m am tel $
             toAbstract insideDecls
          let scope = mapScopeInfo (restrictLocalPrivate am) insideScope
          setScope scope
          return $ TopLevelInfo (outsideDecls ++ insideDecls) scope

        -- We already inserted the missing top-level module, see
        -- 'Agda.Syntax.Parser.Parser.figureOutTopLevelModule',
        -- thus, this case is impossible:
        _ -> __IMPOSSIBLE__

-- | runs Syntax.Concrete.Definitions.niceDeclarations on main module
niceDecls :: DoWarn -> [C.Declaration] -> ([NiceDeclaration] -> ScopeM a) -> ScopeM a
niceDecls warn ds ret = setCurrentRange ds $ computeFixitiesAndPolarities warn ds $ do
  fixs <- scopeFixities <$> getScope  -- We need to pass the fixities to the nicifier for clause grouping
  let (result, warns') = runNice $ niceDeclarations fixs ds

  -- COMPILED pragmas are not allowed in safe mode unless we are in a builtin module.
  -- So we start by filtering out all the PragmaCompiled warnings if one of these two
  -- conditions is not met.
  isSafe    <- Lens.getSafeMode <$> pragmaOptions
  isBuiltin <- Lens.isBuiltinModule . filePath =<< getCurrentPath
  let warns = if isSafe && not isBuiltin then warns' else filter notOnlyInSafeMode warns'

  unless (null warns) $ do
    -- If there are some warnings and the --safe flag is set,
    -- we check that none of the NiceWarnings are fatal
    when isSafe $ do
      let isUnsafe w = declarationWarningName w `elem`
            [ PragmaNoTerminationCheck_
            , PragmaCompiled_
            , MissingDefinitions_
            ]
      let (errs, ws) = List.partition isUnsafe warns
      -- If some of them are, we fail
      unless (null errs) $ do
        warnings $ NicifierIssue <$> ws
        tcerrs <- mapM warning_ $ NicifierIssue <$> errs
        setCurrentRange errs $ typeError $ NonFatalErrors tcerrs
    -- Otherwise we simply record the warnings
    warnings $ NicifierIssue <$> warns
  case result of
    Left e   -> throwError $ Exception (getRange e) $ pretty e
    Right ds -> ret ds

  where notOnlyInSafeMode = (PragmaCompiled_ /=) . declarationWarningName

instance {-# OVERLAPPING #-} ToAbstract [C.Declaration] [A.Declaration] where
  toAbstract ds = do
    -- When --safe is active the termination checker (Issue 586) and
    -- positivity checker (Issue 1614) may not be switched off, and
    -- polarities may not be assigned.
    ds <- ifM (Lens.getSafeMode <$> commandLineOptions)
              (mapM (noNoTermCheck >=> noNoPositivityCheck >=> noPolarity >=> noNoUniverseCheck) ds)
              (return ds)
    niceDecls DoWarn ds toAbstract
   where
    -- ASR (31 December 2015). We don't pattern-match on
    -- @NoTerminationCheck@ because the @NO_TERMINATION_CHECK@ pragma
    -- was removed. See Issue 1763.
    noNoTermCheck :: C.Declaration -> TCM C.Declaration
    noNoTermCheck d@(C.Pragma (C.TerminationCheckPragma r NonTerminating)) =
      d <$ (setCurrentRange d $ warning SafeFlagNonTerminating)
    noNoTermCheck d@(C.Pragma (C.TerminationCheckPragma r Terminating)) =
      d <$ (setCurrentRange d $ warning SafeFlagTerminating)
    noNoTermCheck d = return d

    noNoPositivityCheck :: C.Declaration -> TCM C.Declaration
    noNoPositivityCheck d@(C.Pragma (C.NoPositivityCheckPragma _)) =
      d <$ (setCurrentRange d $ warning SafeFlagNoPositivityCheck)
    noNoPositivityCheck d = return d

    noPolarity :: C.Declaration -> TCM C.Declaration
    noPolarity d@(C.Pragma C.PolarityPragma{}) =
      d <$ (setCurrentRange d $ warning SafeFlagPolarity)
    noPolarity d                               = return d

    noNoUniverseCheck :: C.Declaration -> TCM C.Declaration
    noNoUniverseCheck d@(C.Pragma (C.NoUniverseCheckPragma _)) =
      d <$ (setCurrentRange d $ warning SafeFlagNoUniverseCheck)
    noNoUniverseCheck d = return d

newtype LetDefs = LetDefs [C.Declaration]
newtype LetDef = LetDef NiceDeclaration

instance ToAbstract LetDefs [A.LetBinding] where
  toAbstract (LetDefs ds) =
    concat <$> (niceDecls DoWarn ds $ toAbstract . map LetDef)

instance ToAbstract LetDef [A.LetBinding] where
  toAbstract (LetDef d) =
    case d of
      NiceMutual _ _ _ d@[C.FunSig _ _ _ instanc macro info _ x t, C.FunDef _ _ abstract _ _ _ [cl]] ->
          do  when (abstract == AbstractDef) $ do
                genericError $ "abstract not allowed in let expressions"
              when (macro == MacroDef) $ do
                genericError $ "Macros cannot be defined in a let expression."
              t <- toAbstract t
              -- We bind the name here to make sure it's in scope for the LHS (#917).
              -- It's unbound for the RHS in letToAbstract.
              fx <- getConcreteFixity x
              x  <- A.unBind <$> toAbstract (NewName LetBound $ mkBoundName x fx)
              (x', e) <- letToAbstract cl
              -- If InstanceDef set info to Instance
              let info' | instanc == InstanceDef = makeInstance info
                        | otherwise              = info
              -- There are sometimes two instances of the
              -- let-bound variable, one declaration and one
              -- definition. The first list element below is
              -- used to highlight the declared instance in the
              -- right way (see Issue 1618).
              return [ A.LetDeclaredVariable (A.BindName (setRange (getRange x') x))
                     , A.LetBind (LetRange $ getRange d) info' (A.BindName x) t e
                     ]

      -- irrefutable let binding, like  (x , y) = rhs
      NiceFunClause r PublicAccess ConcreteDef termCheck catchall d@(C.FunClause lhs@(C.LHS p [] []) (C.RHS rhs) NoWhere ca) -> do
        mp  <- setCurrentRange p $
                 (Right <$> parsePattern p)
                   `catchError`
                 (return . Left)
        case mp of
          Right p -> do
            rhs <- toAbstract rhs
            p   <- toAbstract p
            checkPatternLinearity p $ \ys ->
              typeError $ RepeatedVariablesInPattern ys
            bindVarsToBind
            p   <- toAbstract p
            return [ A.LetPatBind (LetRange r) p rhs ]
          -- It's not a record pattern, so it should be a prefix left-hand side
          Left err ->
            case definedName p of
              Nothing -> throwError err
              Just x  -> toAbstract $ LetDef $ NiceMutual r termCheck True
                [ C.FunSig r PublicAccess ConcreteDef NotInstanceDef NotMacroDef defaultArgInfo termCheck x (C.Underscore (getRange x) Nothing)
                , C.FunDef r __IMPOSSIBLE__ ConcreteDef NotInstanceDef __IMPOSSIBLE__ __IMPOSSIBLE__
                  [C.Clause x (ca || catchall) lhs (C.RHS rhs) NoWhere []]
                ]
            where
              definedName (C.IdentP (C.QName x)) = Just x
              definedName C.IdentP{}             = Nothing
              definedName (C.RawAppP _ (p : _))  = definedName p
              definedName (C.ParenP _ p)         = definedName p
              definedName C.WildP{}              = Nothing   -- for instance let _ + x = x in ... (not allowed)
              definedName C.AbsurdP{}            = Nothing
              definedName C.AsP{}                = Nothing
              definedName C.DotP{}               = Nothing
              definedName C.EqualP{}             = Nothing
              definedName C.LitP{}               = Nothing
              definedName C.RecP{}               = Nothing
              definedName C.QuoteP{}             = Nothing
              definedName C.HiddenP{}            = Nothing -- Not impossible, see issue #2291
              definedName C.InstanceP{}          = Nothing
              definedName C.WithP{}              = Nothing
              definedName C.RawAppP{}            = __IMPOSSIBLE__
              definedName C.AppP{}               = __IMPOSSIBLE__
              definedName C.OpAppP{}             = __IMPOSSIBLE__
              definedName C.EllipsisP{}          = __IMPOSSIBLE__

      -- You can't open public in a let
      NiceOpen r x dirs -> do
        when (publicOpen dirs) $ warning UselessPublic
        m    <- toAbstract (OldModuleName x)
        adir <- openModule_ LetOpenModule x dirs
        let minfo = ModuleInfo
              { minfoRange  = r
              , minfoAsName = Nothing
              , minfoAsTo   = renamingRange dirs
              , minfoOpenShort = Nothing
              , minfoDirective = Just dirs
              }
        return [A.LetOpen minfo m adir]

      NiceModuleMacro r p x modapp open dir -> do
        when (publicOpen dir) $ warning UselessPublic
        -- Andreas, 2014-10-09, Issue 1299: module macros in lets need
        -- to be private
        checkModuleMacro LetApply LetOpenModule r (PrivateAccess Inserted) x modapp open dir

      _   -> notAValidLetBinding d
    where
        letToAbstract (C.Clause top catchall clhs@(C.LHS p [] []) (C.RHS rhs) NoWhere []) = do
{-
            p    <- parseLHS top p
            localToAbstract (snd $ lhsArgs p) $ \args ->
-}
            (x, args) <- do
              res <- setCurrentRange p $ parseLHS (C.QName top) p
              case res of
                C.LHSHead x args -> return (x, args)
                C.LHSProj{} -> genericError $ "copatterns not allowed in let bindings"
                C.LHSWith{} -> genericError $ "with-patterns not allowed in let bindings"

            e <- localToAbstract args $ \args -> do
                bindVarsToBind
                -- Make sure to unbind the function name in the RHS, since lets are non-recursive.
                rhs <- unbindVariable top $ toAbstract rhs
                foldM lambda rhs (reverse args)  -- just reverse because these DomainFree
            return (x, e)
        letToAbstract _ = notAValidLetBinding d

        -- Named patterns not allowed in let definitions
        lambda e (Arg info (Named Nothing (A.VarP x))) =
                return $ A.Lam i (A.DomainFree $ unnamedArg info x) e
            where i = ExprRange (fuseRange x e)
        lambda e (Arg info (Named Nothing (A.WildP i))) =
            do  x <- freshNoName (getRange i)
                return $ A.Lam i' (A.DomainFree $ unnamedArg info $ A.BindName x) e
            where i' = ExprRange (fuseRange i e)
        lambda _ _ = notAValidLetBinding d

newtype Blind a = Blind { unBlind :: a }

instance ToAbstract (Blind a) (Blind a) where
  toAbstract = return

-- The only reason why we return a list is that open declarations disappears.
-- For every other declaration we get a singleton list.
instance ToAbstract NiceDeclaration A.Declaration where

  toAbstract d = annotateDecls $
    traceSLn "scope.decl.trace" 50 (unlines
      [ "scope checking declaration"
      , "  " ++  prettyShow d
      ]) $
    traceCall (ScopeCheckDeclaration d) $
    -- Andreas, 2015-10-05, Issue 1677:
    -- We record in the environment whether we are scope checking an
    -- abstract definition.  This way, we can propagate this attribute
    -- the extended lambdas.
    caseMaybe (niceHasAbstract d) id (\ a -> localTC $ \ e -> e { envAbstractMode = aDefToMode a }) $
    case d of

  -- Axiom (actual postulate)
    C.Axiom r p a i rel x t -> do
      -- check that we do not postulate in --safe mode, unless it is a
      -- builtin module with safe postulates
      whenM ((return . Lens.getSafeMode =<< commandLineOptions) `and2M`
             (not <$> (Lens.isBuiltinModuleWithSafePostulates . filePath =<< getCurrentPath)))
            (warning $ SafeFlagPostulate x)
      -- check the postulate
      toAbstractNiceAxiom A.NoFunSig NotMacroDef d

    C.NiceGeneralize r p i x t -> do
      reportSLn "scope.decl" 10 $ "found nice generalize: " ++ prettyShow x
      t_ <- toAbstractCtx TopCtx t
      let (s, t) = unGeneralized t_
      reportSLn "scope.decl" 50 $ "generalizations: " ++ show (Set.toList s, t)
      f <- getConcreteFixity x
      y <- freshAbstractQName f x
      bindName p GeneralizeName x y
      return [A.Generalize s (mkDefInfoInstance x f p ConcreteDef NotInstanceDef NotMacroDef r) i y t]

  -- Fields
    C.NiceField r p a i x t -> do
      unless (p == PublicAccess) $ genericError "Record fields can not be private"
      -- Interaction points for record fields have already been introduced
      -- when checking the type of the record constructor.
      -- To avoid introducing interaction points (IP) twice, we turn
      -- all question marks to underscores.  (See issue 1138.)
      let maskIP (C.QuestionMark r _) = C.Underscore r Nothing
          maskIP e                     = e
      t' <- toAbstractCtx TopCtx $ mapExpr maskIP t
      f  <- getConcreteFixity x
      y  <- freshAbstractQName f x
      -- Andreas, 2018-06-09 issue #2170
      -- We want dependent irrelevance without irrelevant projections,
      -- thus, do not disable irrelevant projections via the scope checker.
      -- irrProj <- optIrrelevantProjections <$> pragmaOptions
      -- unless (isIrrelevant t && not irrProj) $
      --   -- Andreas, 2010-09-24: irrelevant fields are not in scope
      --   -- this ensures that projections out of irrelevant fields cannot occur
      --   -- Ulf: unless you turn on --irrelevant-projections
      do
        bindName p FldName x y
      return [ A.Field (mkDefInfoInstance x f p a i NotMacroDef r) y t' ]

  -- Primitive function
    PrimitiveFunction r p a x t -> do
      t' <- toAbstractCtx TopCtx t
      f  <- getConcreteFixity x
      y  <- freshAbstractQName f x
      bindName p DefName x y
      return [ A.Primitive (mkDefInfo x f p a r) y t' ]

  -- Definitions (possibly mutual)
    NiceMutual r termCheck pc ds -> do
      ds' <- toAbstract ds
      -- We only termination check blocks that do not have a measure.
      return [ A.Mutual (MutualInfo termCheck pc r) ds' ]

    C.NiceRecSig r p a _pc _uc x ls t -> do
      ensureNoLetStms ls
      withLocalVars $ do
        -- Minor hack: record types don't have indices so we include t when
        -- computing generalised parameters, but in the type checker any named
        -- generalizable arguments in the sort should be bound variables.
        (ls', _) <- toAbstract (GenTelAndType (map makeDomainFull ls) t)
        t'  <- toAbstract t
        f   <- getConcreteFixity x
        x'  <- freshAbstractQName f x
        bindName' p DefName (GeneralizedVarsMetadata $ generalizeTelVars ls') x x'
        return [ A.RecSig (mkDefInfo x f p a r) x' ls' t' ]

    C.NiceDataSig r p a _pc _uc x ls t -> withLocalVars $ do
        reportSLn "scope.data.sig" 20 ("checking DataSig for " ++ prettyShow x)
        ensureNoLetStms ls
        withLocalVars $ do
          ls' <- toAbstract $ GenTel $ map makeDomainFull ls
          t'  <- toAbstract $ C.Generalized t
          f  <- getConcreteFixity x
          x' <- freshAbstractQName f x
          bindName' p DefName (GeneralizedVarsMetadata $ generalizeTelVars ls') x x'
          return [ A.DataSig (mkDefInfo x f p a r) x' ls' t' ]

  -- Type signatures
    C.FunSig r p a i m rel tc x t ->
        toAbstractNiceAxiom A.FunSig m (C.Axiom r p a i rel x t)

  -- Function definitions
    C.FunDef r ds a i tc x cs -> do
        printLocals 10 $ "checking def " ++ prettyShow x
        (x',cs) <- toAbstract (OldName x,cs)
        -- Andreas, 2017-12-04 the name must reside in the current module
        unlessM ((A.qnameModule x' ==) <$> getCurrentModule) $
          __IMPOSSIBLE__
        let delayed = NotDelayed
        -- (delayed, cs) <- translateCopatternClauses cs -- TODO
        f <- getConcreteFixity x
        return [ A.FunDef (mkDefInfoInstance x f PublicAccess a i NotMacroDef r) x' delayed cs ]

  -- Uncategorized function clauses
    C.NiceFunClause r acc abs termCheck catchall (C.FunClause lhs rhs wcls ca) ->
      genericError $
        "Missing type signature for left hand side " ++ prettyShow lhs
    C.NiceFunClause{} -> __IMPOSSIBLE__

  -- Data definitions
    C.NiceDataDef r o a _ uc x pars cons -> withLocalVars $ do
        reportSLn "scope.data.def" 20 ("checking " ++ show o ++ " DataDef for " ++ prettyShow x)
        (p, ax) <- resolveName (C.QName x) >>= \case
          DefinedName p ax -> do
            livesInCurrentModule ax  -- Andreas, 2017-12-04, issue #2862
            return (p, ax)
          _ -> genericError $ "Missing type signature for data definition " ++ prettyShow x
        ensureNoLetStms pars
        withLocalVars $ do
          gvars <- bindGeneralizablesIfInserted o ax
          -- Check for duplicate constructors
          do cs <- mapM conName cons
             let dups = nub $ cs \\ nub cs
                 bad  = filter (`elem` dups) cs
             unless (distinct cs) $
               setCurrentRange bad $
                 typeError $ DuplicateConstructors dups

          pars <- toAbstract pars
          let x' = anameName ax
          -- Create the module for the qualified constructors
          checkForModuleClash x -- disallow shadowing previously defined modules
          let m = mnameFromList $ qnameToList x'
          createModule (Just IsData) m
          bindModule p x m  -- make it a proper module
          cons <- toAbstract (map (ConstrDecl NoRec m a p) cons)
          printScope "data" 20 $ "Checked data " ++ prettyShow x
          f <- getConcreteFixity x
          return [ A.DataDef (mkDefInfo x f PublicAccess a r) x' uc (DataDefParams gvars pars) cons ]
      where
        conName (C.Axiom _ _ _ _ _ c _) = return c
        conName d = errorNotConstrDecl d

  -- Record definitions (mucho interesting)
    C.NiceRecDef r o a _ uc x ind eta cm pars fields -> do
      reportSLn "scope.rec.def" 20 ("checking " ++ show o ++ " RecDef for " ++ prettyShow x)
      (p, ax) <- resolveName (C.QName x) >>= \case
        DefinedName p ax -> do
          livesInCurrentModule ax  -- Andreas, 2017-12-04, issue #2862
          return (p, ax)
        _ -> genericError $ "Missing type signature for record definition " ++ prettyShow x
      ensureNoLetStms pars
      withLocalVars $ do
        gvars <- bindGeneralizablesIfInserted o ax
        -- Check that the generated module doesn't clash with a previously
        -- defined module
        checkForModuleClash x
        pars   <- toAbstract pars
        let x' = anameName ax
        -- We scope check the fields a first time when putting together
        -- the type of the constructor.
        contel <- localToAbstract (RecordConstructorType fields) return
        m0     <- getCurrentModule
        let m = A.qualifyM m0 $ mnameFromList [ last $ qnameToList x' ]
        printScope "rec" 15 "before record"
        createModule (Just IsRecord) m
        -- We scope check the fields a second time, as actual fields.
        afields <- withCurrentModule m $ do
          afields <- toAbstract fields
          printScope "rec" 15 "checked fields"
          return afields
        -- Andreas, 2017-07-13 issue #2642 disallow duplicate fields
        -- Check for duplicate fields. (See "Check for duplicate constructors")
        do let fs = forMaybe fields $ \case
                 C.Field _ f _ -> Just f
                 _ -> Nothing
           let dups = nub $ fs \\ nub fs
               bad  = filter (`elem` dups) fs
           unless (distinct fs) $
             setCurrentRange bad $
               typeError $ DuplicateFields dups
        bindModule p x m
        cm' <- mapM (\(c, _) -> bindConstructorName m c a p YesRec) cm
        let inst = caseMaybe cm NotInstanceDef snd
        printScope "rec" 15 "record complete"
        f <- getConcreteFixity x
        let params = DataDefParams gvars pars
        return [ A.RecDef (mkDefInfoInstance x f PublicAccess a inst NotMacroDef r) x' uc ind eta cm' params contel afields ]

    NiceModule r p a x@(C.QName name) tel ds -> do
      reportSDoc "scope.decl" 70 $ vcat $
        [ text $ "scope checking NiceModule " ++ prettyShow x
        ]

      adecls <- traceCall (ScopeCheckDeclaration $ NiceModule r p a x tel []) $ do
        scopeCheckNiceModule r p name tel $ toAbstract ds

      reportSDoc "scope.decl" 70 $ vcat $
        [ text $ "scope checked NiceModule " ++ prettyShow x
        ] ++ map (nest 2 . prettyA) adecls
      return adecls

    NiceModule _ _ _ m@C.Qual{} _ _ ->
      genericError $ "Local modules cannot have qualified names"

    NiceModuleMacro r p x modapp open dir -> do
      reportSDoc "scope.decl" 70 $ vcat $
        [ text $ "scope checking NiceModuleMacro " ++ prettyShow x
        ]

      adecls <- checkModuleMacro Apply TopOpenModule r p x modapp open dir

      reportSDoc "scope.decl" 70 $ vcat $
        [ text $ "scope checked NiceModuleMacro " ++ prettyShow x
        ] ++ map (nest 2 . prettyA) adecls
      return adecls

    NiceOpen r x dir -> do
      (minfo, m, adir) <- checkOpen r x dir
      return [A.Open minfo m adir]

    NicePragma r p -> do
      ps <- toAbstract p
      return $ map (A.Pragma r) ps

    NiceImport r x as open dir -> setCurrentRange r $ do
      notPublicWithoutOpen open dir

      -- Andreas, 2018-11-03, issue #3364, parse expression in as-clause as Name.
      let illformedAs s = traceCall (SetRange $ getRange as) $ do
            -- If @as@ is followed by something that is not a simple name,
            -- throw a warning and discard the as-clause.
            Nothing <$ warning (IllformedAsClause s)
      as <- case as of
        -- Ok if no as-clause or it (already) contains a Name.
        Nothing -> return Nothing
        Just (AsName (Right asName) r)                    -> return $ Just $ AsName asName r
        Just (AsName (Left (C.Ident (C.QName asName))) r) -> return $ Just $ AsName asName r
        Just (AsName (Left (C.Ident C.Qual{})) r) -> illformedAs "; a qualified name is not allowed here"
        Just (AsName (Left C.Underscore{})     r) -> illformedAs "; an underscore is not allowed here"
        Just (AsName (Left e)                  r) -> illformedAs ""

      -- First scope check the imported module and return its name and
      -- interface. This is done with that module as the top-level module.
      -- This is quite subtle. We rely on the fact that when setting the
      -- top-level module and generating a fresh module name, the generated
      -- name will be exactly the same as the name generated when checking
      -- the imported module.
      (m, i) <- withCurrentModule noModuleName $ withTopLevelModule x $ do
        m <- toAbstract $ NewModuleQName x
        printScope "import" 10 "before import:"
        (m, i) <- scopeCheckImport m
        printScope "import" 10 $ "scope checked import: " ++ show i
        -- We don't want the top scope of the imported module (things happening
        -- before the module declaration)
        return (m, Map.delete noModuleName i)

      -- Merge the imported scopes with the current scopes
      modifyScopes $ \ ms -> Map.unionWith mergeScope (Map.delete m ms) i

      -- Bind the desired module name to the right abstract name.
      case as of
        Nothing -> bindQModule (PrivateAccess Inserted) x m
        Just y  -> bindModule (PrivateAccess Inserted) (asName y) m

      printScope "import" 10 "merged imported sig:"

      -- Open if specified, otherwise apply import directives
      let (name, theAsSymbol, theAsName) = case as of
            Nothing -> (x,                  noRange,   Nothing)
            Just a  -> (C.QName (asName a), asRange a, Just (asName a))
      adir <- case open of
        DoOpen   -> do
          (_minfo, _m, adir) <- checkOpen r name dir
          return adir
        -- If not opening, import directives are applied to the original scope.
        DontOpen -> modifyNamedScopeM m $ applyImportDirectiveM x dir
      let minfo = ModuleInfo
            { minfoRange     = r
            , minfoAsName    = theAsName
            , minfoAsTo      = getRange (theAsSymbol, renamingRange dir)
            , minfoOpenShort = Just open
            , minfoDirective = Just dir
            }
      return [ A.Import minfo m adir ]

    NiceUnquoteDecl r p a i tc xs e -> do
      fxs <- mapM getConcreteFixity xs
      ys <- zipWithM freshAbstractQName fxs xs
      zipWithM_ (bindName p QuotableName) xs ys
      e <- toAbstract e
      zipWithM_ (rebindName p DefName) xs ys
      let mi = MutualInfo tc True r
      return [ A.Mutual mi [A.UnquoteDecl mi [ mkDefInfoInstance x fx p a i NotMacroDef r | (fx, x) <- zip fxs xs ] ys e] ]

    NiceUnquoteDef r p a tc xs e -> do
      fxs <- mapM getConcreteFixity xs
      ys <- mapM (toAbstract . OldName) xs
      zipWithM_ (rebindName p QuotableName) xs ys
      e <- toAbstract e
      zipWithM_ (rebindName p DefName) xs ys
      return [ A.UnquoteDef [ mkDefInfo x fx PublicAccess a r | (fx, x) <- zip fxs xs ] ys e ]

    NicePatternSyn r n as p -> do
      reportSLn "scope.pat" 10 $ "found nice pattern syn: " ++ prettyShow n
      (as, p) <- withLocalVars $ do
         p  <- toAbstract =<< parsePatternSyn p
         checkPatternLinearity p $ \ys ->
           typeError $ RepeatedVariablesInPattern ys
         bindVarsToBind
         let err = "Dot or equality patterns are not allowed in pattern synonyms. Maybe use '_' instead."
         p <- noDotorEqPattern err p
         as <- (traverse . mapM) (unVarName <=< resolveName . C.QName) as
         unlessNull (patternVars p \\ map unArg as) $ \ xs -> do
           typeError . GenericDocError =<< do
             "Unbound variables in pattern synonym: " <+>
               sep (map prettyA xs)
         return (as, p)
      y <- freshAbstractQName' n
      bindName PublicAccess PatternSynName n y
      -- Expanding pattern synonyms already at definition makes it easier to
      -- fold them back when printing (issue #2762).
      ep <- expandPatternSynonyms p
      modifyPatternSyns (Map.insert y (as, ep))
      return [A.PatternSynDef y as p]   -- only for highlighting, so use unexpanded version
      where unVarName (VarName a _) = return a
            unVarName _ = typeError $ UnusedVariableInPatternSynonym

    where
      -- checking postulate or type sig. without checking safe flag
      toAbstractNiceAxiom funSig isMacro (C.Axiom r p a i info x t) = do
        t' <- toAbstractCtx TopCtx t
        f  <- getConcreteFixity x
        mp <- getConcretePolarity x
        y  <- freshAbstractQName f x
        let kind | isMacro == MacroDef = MacroName
                 | otherwise           = DefName
        bindName p kind x y
        return [ A.Axiom funSig (mkDefInfoInstance x f p a i isMacro r) info mp y t' ]
      toAbstractNiceAxiom _ _ _ = __IMPOSSIBLE__

unGeneralized :: A.Expr -> (Set.Set I.QName, A.Expr)
unGeneralized (A.Generalized s t) = (s, t)
unGeneralized (A.ScopedExpr si e) = A.ScopedExpr si <$> unGeneralized e
unGeneralized t = (mempty, t)

collectGeneralizables :: ScopeM a -> ScopeM (Set I.QName, a)
collectGeneralizables m = bracket_ open close $ do
    a <- m
    s <- useTC stGeneralizedVars
    case s of
        Nothing -> __IMPOSSIBLE__
        Just s -> return (s, a)
  where
    open = do
        gvs <- useTC stGeneralizedVars
        stGeneralizedVars `setTCLens` Just mempty
        pure gvs
    close = (stGeneralizedVars `setTCLens`)

createBoundNamesForGeneralizables :: Set I.QName -> ScopeM (Map I.QName I.Name)
createBoundNamesForGeneralizables vs =
  flip Map.traverseWithKey (Map.fromSet (const ()) vs) $ \ q _ -> do
    let x  = nameConcrete $ qnameName q
        fx = nameFixity   $ qnameName q
    freshAbstractName fx x

collectAndBindGeneralizables :: ScopeM a -> ScopeM (Map I.QName I.Name, a)
collectAndBindGeneralizables m = do
  (s, res) <- collectGeneralizables m
  -- We should bind the named generalizable variables as fresh variables
  binds <- createBoundNamesForGeneralizables s
  bindGeneralizables binds
  return (binds, res)

bindGeneralizables :: Map A.QName A.Name -> ScopeM ()
bindGeneralizables vars =
  forM_ (Map.toList vars) $ \ (q, y) ->
    bindVariable LambdaBound (nameConcrete $ qnameName q) y

-- | Bind generalizable variables if data or record decl was split by the system
--   (origin == Inserted)
bindGeneralizablesIfInserted :: Origin -> AbstractName -> ScopeM (Set A.Name)
bindGeneralizablesIfInserted Inserted y = bound <$ bindGeneralizables gvars
  where gvars = case anameMetadata y of
          GeneralizedVarsMetadata gvars -> gvars
          NoMetadata                    -> Map.empty
        bound = Set.fromList (Map.elems gvars)
bindGeneralizablesIfInserted UserWritten _ = return Set.empty
bindGeneralizablesIfInserted _ _           = __IMPOSSIBLE__

newtype GenTel = GenTel C.Telescope
data GenTelAndType = GenTelAndType C.Telescope C.Expr

instance ToAbstract GenTel A.GeneralizeTelescope where
  toAbstract (GenTel tel) =
    uncurry A.GeneralizeTel <$> collectAndBindGeneralizables (toAbstract tel)

instance ToAbstract GenTelAndType (A.GeneralizeTelescope, A.Expr) where
  toAbstract (GenTelAndType tel t) = do
    (binds, (tel, t)) <- collectAndBindGeneralizables $
                          (,) <$> toAbstract tel <*> toAbstract t
    return (A.GeneralizeTel binds tel, t)

-- | Make sure definition is in same module as signature.
class LivesInCurrentModule a where
  livesInCurrentModule :: a -> ScopeM ()

instance LivesInCurrentModule AbstractName where
  livesInCurrentModule = livesInCurrentModule . anameName

instance LivesInCurrentModule A.QName where
  livesInCurrentModule x = do
    m <- getCurrentModule
    reportSLn "scope.data.def" 30 $ unlines
      [ "  A.QName of data type: " ++ show x
      , "  current module: " ++ show m
      ]
    unless (A.qnameModule x == m) $
      genericError $ "Definition in different module than its type signature"

data IsRecordCon = YesRec | NoRec
data ConstrDecl = ConstrDecl IsRecordCon A.ModuleName IsAbstract Access C.NiceDeclaration

bindConstructorName :: ModuleName -> C.Name -> IsAbstract ->
                       Access -> IsRecordCon -> ScopeM A.QName
bindConstructorName m x a p record = do
  f <- getConcreteFixity x
  -- The abstract name is the qualified one
  y <- withCurrentModule m $ freshAbstractQName f x
  -- Bind it twice, once unqualified and once qualified
  bindName p' ConName x y
  withCurrentModule m $ bindName p'' ConName x y
  return y
  where
    -- An abstract constructor is private (abstract constructor means
    -- abstract datatype, so the constructor should not be exported).
    p' = case a of
           AbstractDef -> PrivateAccess Inserted
           _           -> p
    p'' = case (a, record) of
            (AbstractDef, _) -> PrivateAccess Inserted
            (_, YesRec)      -> OnlyQualified   -- record constructors aren't really in the record module
            _                -> PublicAccess

instance ToAbstract ConstrDecl A.Declaration where
  toAbstract (ConstrDecl record m a p d) = do
    case d of
      C.Axiom r p1 a1 i info x t -> do -- rel==Relevant
        -- unless (p1 == p) __IMPOSSIBLE__  -- This invariant is currently violated by test/Succeed/Issue282.agda
        unless (a1 == a) __IMPOSSIBLE__
        t' <- toAbstractCtx TopCtx t
        -- The abstract name is the qualified one
        -- Bind it twice, once unqualified and once qualified
        f <- getConcreteFixity x
        y <- bindConstructorName m x a p record
        printScope "con" 15 "bound constructor"
        return $ A.Axiom NoFunSig (mkDefInfoInstance x f p a i NotMacroDef r)
                         info Nothing y t'
      _ -> errorNotConstrDecl d

errorNotConstrDecl :: C.NiceDeclaration -> ScopeM a
errorNotConstrDecl d = typeError . GenericDocError $
        "Illegal declaration in data type definition " P.$$
        P.nest 2 (P.vcat $ map pretty (notSoNiceDeclarations d))

instance ToAbstract C.Pragma [A.Pragma] where
  toAbstract (C.ImpossiblePragma _) = impossibleTest
  toAbstract (C.OptionsPragma _ opts) = return [ A.OptionsPragma opts ]
  toAbstract (C.RewritePragma _ []) = [] <$ warning EmptyRewritePragma
  toAbstract (C.RewritePragma _ xs) = concat <$> do
   forM xs $ \ x -> do
    e <- toAbstract $ OldQName x Nothing
    case e of
      A.Def x          -> return [ A.RewritePragma x ]
      A.Proj _ p | Just x <- getUnambiguous p -> return [ A.RewritePragma x ]
      A.Proj _ x       -> genericError $ "REWRITE used on ambiguous name " ++ prettyShow x
      A.Con c | Just x <- getUnambiguous c -> return [ A.RewritePragma x ]
      A.Con x          -> genericError $ "REWRITE used on ambiguous name " ++ prettyShow x
      A.Var x          -> genericError $ "REWRITE used on parameter " ++ prettyShow x ++ " instead of on a defined symbol"
      _       -> __IMPOSSIBLE__
  toAbstract (C.ForeignPragma _ b s) = [] <$ addForeignCode b s
  toAbstract (C.CompilePragma _ b x s) = do
    e <- toAbstract $ OldQName x Nothing
    let err what = genericError $ "Cannot COMPILE " ++ what ++ " " ++ prettyShow x
    y <- case e of
          A.Def x             -> return x
          A.Proj _ p | Just x <- getUnambiguous p -> return x
          A.Proj _ x          -> err "ambiguous projection"
          A.Con c | Just x <- getUnambiguous c -> return x
          A.Con x             -> err "ambiguous constructor"
          A.PatternSyn{}      -> err "pattern synonym"
          A.Var{}             -> err "local variable"
          _                   -> __IMPOSSIBLE__
    return [ A.CompilePragma b y s ]

  toAbstract (C.StaticPragma _ x) = do
      e <- toAbstract $ OldQName x Nothing
      y <- case e of
          A.Def  x -> return x
          A.Proj _ p | Just x <- getUnambiguous p -> return x
          A.Proj _ x -> genericError $
            "STATIC used on ambiguous name " ++ prettyShow x
          _        -> genericError "Target of STATIC pragma should be a function"
      return [ A.StaticPragma y ]
  toAbstract (C.InjectivePragma _ x) = do
      e <- toAbstract $ OldQName x Nothing
      y <- case e of
          A.Def  x -> return x
          A.Proj _ p | Just x <- getUnambiguous p -> return x
          A.Proj _ x -> genericError $
            "INJECTIVE used on ambiguous name " ++ prettyShow x
          _        -> genericError "Target of INJECTIVE pragma should be a defined symbol"
      return [ A.InjectivePragma y ]
  toAbstract (C.InlinePragma _ b x) = do
      e <- toAbstract $ OldQName x Nothing
      let sINLINE = if b then "INLINE" else "NOINLINE"
      y <- case e of
          A.Def  x -> return x
          A.Proj _ p | Just x <- getUnambiguous p -> return x
          A.Proj _ x -> genericError $
            sINLINE ++ " used on ambiguous name " ++ prettyShow x
          _        -> genericError $ "Target of " ++ sINLINE ++ " pragma should be a function"
      return [ A.InlinePragma b y ]
  toAbstract (C.BuiltinPragma _ b q) | isUntypedBuiltin b = do
    bindUntypedBuiltin b =<< toAbstract (ResolveQName q)
    return []
  toAbstract (C.BuiltinPragma _ b q) = do
    -- Andreas, 2015-02-14
    -- Some builtins cannot be given a valid Agda type,
    -- thus, they do not come with accompanying postulate or definition.
    if b `elem` builtinsNoDef then do
      case q of
        C.QName x -> do
          -- The name shouldn't exist yet. If it does, we raise a warning
          -- and drop the existing definition.
          unlessM ((UnknownName ==) <$> resolveName q) $ do
            genericWarning $ P.text $
               "BUILTIN " ++ b ++ " declares an identifier " ++
               "(no longer expects an already defined identifier)"
            modifyCurrentScope $ removeNameFromScope PublicNS x
          -- We then happily bind the name
          y <- freshAbstractQName' x
          kind <- fromMaybe __IMPOSSIBLE__ <$> builtinKindOfName b
          bindName PublicAccess kind x y
          return [ A.BuiltinNoDefPragma b y ]
        _ -> genericError $
          "Pragma BUILTIN " ++ b ++ ": expected unqualified identifier, " ++
          "but found " ++ prettyShow q
    else do
      q <- toAbstract $ ResolveQName q
      return [ A.BuiltinPragma b q ]
  toAbstract (C.EtaPragma _ x) = do
    e <- toAbstract $ OldQName x Nothing
    case e of
      A.Def x -> return [ A.EtaPragma x ]
      _       -> do
       e <- showA e
       genericError $ "Pragma ETA: expected identifier, " ++
         "but found expression " ++ e
  toAbstract (C.DisplayPragma _ lhs rhs) = withLocalVars $ do
    let err = genericError "DISPLAY pragma left-hand side must have form 'f e1 .. en'"
        getHead (C.IdentP x)          = return x
        getHead (C.RawAppP _ (p : _)) = getHead p
        getHead _                     = err

    top <- getHead lhs

    (isPatSyn, hd) <- do
      qx <- resolveName' allKindsOfNames Nothing top
      case qx of
        VarName x' _                -> return . (False,) $ A.qnameFromList [x']
        DefinedName _ d             -> return . (False,) $ anameName d
        FieldName     (d :! [])     -> return . (False,) $ anameName d
        FieldName ds                -> genericError $ "Ambiguous projection " ++ prettyShow top ++ ": " ++ prettyShow (fmap anameName ds)
        ConstructorName (d :! [])   -> return . (False,) $ anameName d
        ConstructorName ds          -> genericError $ "Ambiguous constructor " ++ prettyShow top ++ ": " ++ prettyShow (fmap anameName ds)
        UnknownName                 -> notInScope top
        PatternSynResName (d :! []) -> return . (True,) $ anameName d
        PatternSynResName ds        -> genericError $ "Ambiguous pattern synonym" ++ prettyShow top ++ ": " ++ prettyShow (fmap anameName ds)

    lhs <- toAbstract $ LeftHandSide top lhs
    ps  <- case lhs of
             A.LHS _ (A.LHSHead _ ps) -> return ps
             _ -> err

    -- Andreas, 2016-08-08, issue #2132
    -- Remove pattern synonyms on lhs
    (hd, ps) <- do
      let mkP | isPatSyn  = A.PatternSynP (PatRange $ getRange lhs) (unambiguous hd)
              | otherwise = A.DefP (PatRange $ getRange lhs) (unambiguous hd)
      p <- expandPatternSynonyms $ mkP ps
      case p of
        A.DefP _ f ps | Just hd <- getUnambiguous f -> return (hd, ps)
        A.ConP _ c ps | Just hd <- getUnambiguous c -> return (hd, ps)
        A.PatternSynP{} -> __IMPOSSIBLE__
        _ -> err

    rhs <- toAbstract rhs
    return [A.DisplayPragma hd ps rhs]

  toAbstract (C.WarningOnUsage _ oqn str) = do
    qn <- toAbstract $ OldName oqn
    stLocalUserWarnings `modifyTCLens` Map.insert qn str
    pure []

  toAbstract (C.WarningOnImport _ str) = do
    stWarningOnImport `setTCLens` Just str
    pure []

  -- Termination checking pragmes are handled by the nicifier
  toAbstract C.TerminationCheckPragma{} = __IMPOSSIBLE__

  toAbstract C.CatchallPragma{}         = __IMPOSSIBLE__

  -- No positivity checking pragmas are handled by the nicifier.
  toAbstract C.NoPositivityCheckPragma{} = __IMPOSSIBLE__

  -- Polarity pragmas are handled by the niceifier.
  toAbstract C.PolarityPragma{} = __IMPOSSIBLE__

  -- No universe checking pragmas are handled by the niceifier.
  toAbstract C.NoUniverseCheckPragma{} = __IMPOSSIBLE__

instance ToAbstract C.Clause A.Clause where
  toAbstract (C.Clause top catchall lhs@(C.LHS p eqs with) rhs wh wcs) = withLocalVars $ do
    -- Jesper, 2018-12-10, #3095: pattern variables bound outside the
    -- module are locally treated as module parameters
    modifyScope_ $ updateScopeLocals $ map $ second patternToModuleBound
    -- Andreas, 2012-02-14: need to reset local vars before checking subclauses
    vars <- getLocalVars
    let wcs' = for wcs $ \ c -> setLocalVars vars $> c
    lhs' <- toAbstract $ LeftHandSide (C.QName top) p
    printLocals 10 "after lhs:"
    let (whname, whds) = case wh of
          NoWhere        -> (Nothing, [])
          -- Andreas, 2016-07-17 issues #2081 and #2101
          -- where-declarations are automatically private.
          -- This allows their type signature to be checked InAbstractMode.
          AnyWhere ds    -> (Nothing, [C.Private noRange Inserted ds])
          -- Named where-modules do not default to private.
          SomeWhere m a ds -> (Just (m, a), ds)

    let isTerminationPragma :: C.Declaration -> Bool
        isTerminationPragma (C.Private _ _ ds) = any isTerminationPragma ds
        isTerminationPragma (C.Pragma (TerminationCheckPragma _ _)) = True
        isTerminationPragma _                                       = False

    if not (null eqs)
      then do
        rhs <- toAbstract =<< toAbstractCtx TopCtx (RightHandSide eqs with wcs' rhs whds)
        return $ A.Clause lhs' [] rhs A.noWhereDecls catchall
      else do
        -- ASR (16 November 2015) Issue 1137: We ban termination
        -- pragmas inside `where` clause.
        when (any isTerminationPragma whds) $
             genericError "Termination pragmas are not allowed inside where clauses"

        -- the right hand side is checked inside the module of the local definitions
        (rhs, ds) <- whereToAbstract (getRange wh) whname whds $
                      toAbstractCtx TopCtx (RightHandSide eqs with wcs' rhs [])
        rhs <- toAbstract rhs
                 -- #2897: we need to restrict named where modules in refined contexts,
                 --        so remember whether it was named here
        return $ A.Clause lhs' [] rhs ds catchall

whereToAbstract :: Range -> Maybe (C.Name, Access) -> [C.Declaration] -> ScopeM a -> ScopeM (a, A.WhereDeclarations)
whereToAbstract _ whname []   inner = (, A.noWhereDecls) <$> inner
whereToAbstract r whname whds inner = do
  -- Create a fresh concrete name if there isn't (a proper) one.
  (m, acc) <- do
    case whname of
      Just (m, acc) | not (isNoName m) -> return (m, acc)
      _ -> fresh <&> \ x -> (C.NoName (getRange whname) x, PrivateAccess Inserted)
           -- unnamed where's are private
  let tel = []
  old <- getCurrentModule
  am  <- toAbstract (NewModuleName m)
  (scope, ds) <- scopeCheckModule r (C.QName m) am tel $ toAbstract whds
  setScope scope
  x <- inner
  setCurrentModule old
  bindModule acc m am
  -- Issue 848: if the module was anonymous (module _ where) open it public
  let anonymousSomeWhere = maybe False (isNoName . fst) whname
  when anonymousSomeWhere $
   void $ -- We can ignore the returned default A.ImportDirective.
    openModule_ TopOpenModule (C.QName m) $
      defaultImportDir { publicOpen = True }
  return (x, A.WhereDecls (am <$ whname) ds)

data RightHandSide = RightHandSide
  { rhsRewriteEqn :: [C.RewriteEqn]    -- ^ @rewrite e@ (many)
  , rhsWithExpr   :: [C.WithExpr]      -- ^ @with e@ (many)
  , rhsSubclauses :: [ScopeM C.Clause] -- ^ the subclauses spawned by a with (monadic because we need to reset the local vars before checking these clauses)
  , rhs           :: C.RHS
  , rhsWhereDecls :: [C.Declaration]
  }

data AbstractRHS
  = AbsurdRHS'
  | WithRHS' [A.Expr] [ScopeM C.Clause]  -- ^ The with clauses haven't been translated yet
  | RHS' A.Expr C.Expr
  | RewriteRHS' [A.Expr] AbstractRHS A.WhereDeclarations

qualifyName_ :: A.Name -> ScopeM A.QName
qualifyName_ x = do
  m <- getCurrentModule
  return $ A.qualify m x

withFunctionName :: String -> ScopeM A.QName
withFunctionName s = do
  NameId i _ <- fresh
  qualifyName_ =<< freshName_ (s ++ show i)

instance ToAbstract AbstractRHS A.RHS where
  toAbstract AbsurdRHS'            = return A.AbsurdRHS
  toAbstract (RHS' e c)            = return $ A.RHS e $ Just c
  toAbstract (RewriteRHS' eqs rhs wh) = do
    auxs <- replicateM (length eqs) $ withFunctionName "rewrite-"
    rhs  <- toAbstract rhs
    return $ RewriteRHS (zip auxs eqs) [] rhs wh
  toAbstract (WithRHS' es cs) = do
    aux <- withFunctionName "with-"
    A.WithRHS aux es <$> do toAbstract =<< sequence cs

instance ToAbstract RightHandSide AbstractRHS where
  toAbstract (RightHandSide eqs@(_:_) es cs rhs wh) = do
    eqs <- toAbstractCtx TopCtx eqs
                 -- TODO: remember named where
    (rhs, ds) <- whereToAbstract (getRange wh) Nothing wh $
                  toAbstract (RightHandSide [] es cs rhs [])
    return $ RewriteRHS' eqs rhs ds
  toAbstract (RightHandSide [] [] (_ : _) _ _)        = __IMPOSSIBLE__
  toAbstract (RightHandSide [] (_ : _) _ (C.RHS _) _) = typeError $ BothWithAndRHS
  toAbstract (RightHandSide [] [] [] rhs [])          = toAbstract rhs
  toAbstract (RightHandSide [] es cs C.AbsurdRHS [])  = do
    es <- toAbstractCtx TopCtx es
    return $ WithRHS' es cs
  -- TODO: some of these might be possible
  toAbstract (RightHandSide [] (_ : _) _ C.AbsurdRHS (_ : _)) = __IMPOSSIBLE__
  toAbstract (RightHandSide [] [] [] (C.RHS _) (_ : _))       = __IMPOSSIBLE__
  toAbstract (RightHandSide [] [] [] C.AbsurdRHS (_ : _))     = __IMPOSSIBLE__

instance ToAbstract C.RHS AbstractRHS where
    toAbstract C.AbsurdRHS = return $ AbsurdRHS'
    toAbstract (C.RHS e)   = RHS' <$> toAbstract e <*> pure e

data LeftHandSide = LeftHandSide C.QName C.Pattern

instance ToAbstract LeftHandSide A.LHS where
    toAbstract (LeftHandSide top lhs) =
      traceCall (ScopeCheckLHS top lhs) $ do
        lhscore <- parseLHS top lhs
        reportSLn "scope.lhs" 5 $ "parsed lhs: " ++ show lhscore
        printLocals 10 "before lhs:"
        -- error if copattern parsed but --no-copatterns option
        unlessM (optCopatterns <$> pragmaOptions) $
          when (hasCopatterns lhscore) $
            typeError $ NeedOptionCopatterns
        -- scope check patterns except for dot patterns
        lhscore <- toAbstract lhscore
        bindVarsToBind
        reportSLn "scope.lhs" 5 $ "parsed lhs patterns: " ++ show lhscore
        printLocals 10 "checked pattern:"
        -- scope check dot patterns
        lhscore <- toAbstract lhscore
        reportSLn "scope.lhs" 5 $ "parsed lhs dot patterns: " ++ show lhscore
        printLocals 10 "checked dots:"
        return $ A.LHS (LHSRange $ getRange lhs) lhscore

-- Merges adjacent EqualP patterns into one: typecheking expects only one pattern for each domain in the telescope.
mergeEqualPs :: [NamedArg (Pattern' e)] -> [NamedArg (Pattern' e)]
mergeEqualPs = go Nothing
  where
    go acc (Arg i (Named n (A.EqualP r es)) : ps) = go (fmap (fmap (++es)) acc `mplus` Just ((i,n,r),es)) ps
    go Nothing [] = []
    go Nothing (p : ps) = p : go Nothing ps
    go (Just ((i,n,r),es)) ps = Arg i (Named n (A.EqualP r es)) :
      case ps of
        (p : ps) -> p : go Nothing ps
        []     -> []

-- does not check pattern linearity
instance ToAbstract C.LHSCore (A.LHSCore' C.Expr) where
    toAbstract (C.LHSHead x ps) = do
        x <- withLocalVars $ do
          setLocalVars []
          toAbstract (OldName x)
        A.LHSHead x . mergeEqualPs <$> toAbstract ps
    toAbstract (C.LHSProj d ps1 l ps2) = do
        unless (null ps1) $ typeError $ GenericDocError $
          "Ill-formed projection pattern" P.<+> P.pretty (foldl C.AppP (C.IdentP d) ps1)
        qx <- resolveName d
        ds <- case qx of
                FieldName ds -> return $ fmap anameName ds
                UnknownName -> notInScope d
                _           -> genericError $
                  "head of copattern needs to be a field identifier, but "
                  ++ prettyShow d ++ " isn't one"
        A.LHSProj (AmbQ ds) <$> toAbstract l <*> (mergeEqualPs <$> toAbstract ps2)
    toAbstract (C.LHSWith core wps ps) = do
      liftA3 A.LHSWith
        (toAbstract core)
        (toAbstract wps)
        (toAbstract ps)

instance ToAbstract c a => ToAbstract (WithHiding c) (WithHiding a) where
  toAbstract (WithHiding h a) = WithHiding h <$> toAbstractHiding h a

instance ToAbstract c a => ToAbstract (Arg c) (Arg a) where
    toAbstract (Arg info e) =
        Arg info <$> toAbstractHiding info e

instance ToAbstract c a => ToAbstract (Named name c) (Named name a) where
    toAbstract (Named n e) = Named n <$> toAbstract e

{- DOES NOT WORK ANYMORE with pattern synonyms
instance ToAbstract c a => ToAbstract (A.LHSCore' c) (A.LHSCore' a) where
    toAbstract = mapM toAbstract
-}

instance ToAbstract (A.LHSCore' C.Expr) (A.LHSCore' A.Expr) where
    toAbstract (A.LHSHead f ps)         = A.LHSHead f <$> mapM toAbstract ps
    toAbstract (A.LHSProj d lhscore ps) = A.LHSProj d <$> mapM toAbstract lhscore <*> mapM toAbstract ps
    toAbstract (A.LHSWith core wps ps)  = liftA3 A.LHSWith (toAbstract core) (toAbstract wps) (toAbstract ps)

-- Patterns are done in two phases. First everything but the dot patterns, and
-- then the dot patterns. This is because dot patterns can refer to variables
-- bound anywhere in the pattern.

instance ToAbstract (A.Pattern' C.Expr) (A.Pattern' A.Expr) where
  toAbstract = traverse $ insideDotPattern . toAbstractCtx DotPatternCtx  -- Issue #3033

resolvePatternIdentifier ::
  Range -> C.QName -> Maybe (Set A.Name) -> ScopeM (A.Pattern' C.Expr)
resolvePatternIdentifier r x ns = do
  reportSLn "scope.pat" 60 $ "resolvePatternIdentifier " ++ show x ++ " at source position " ++ show r
  px <- toAbstract (PatName x ns)
  case px of
    VarPatName y         -> do
      reportSLn "scope.pat" 60 $ "  resolved to VarPatName " ++ show y ++ " with range " ++ show (getRange y)
      return $ VarP $ A.BindName y
    ConPatName ds        -> return $ ConP (ConPatInfo ConOCon (PatRange r) ConPatEager)
                                          (AmbQ $ fmap anameName ds) []
    PatternSynPatName ds -> return $ PatternSynP (PatRange r)
                                                 (AmbQ $ fmap anameName ds) []

-- | Apply an abstract syntax pattern head to pattern arguments.
--
--   Fails with 'InvalidPattern' if head is not a constructor pattern
--   (or similar) that can accept arguments.
--
applyAPattern
  :: C.Pattern            -- ^ The application pattern in concrete syntax.
  -> A.Pattern' C.Expr    -- ^ Head of application.
  -> NAPs C.Expr          -- ^ Arguments of application.
  -> ScopeM (A.Pattern' C.Expr)
applyAPattern p0 p ps = do
  setRange (getRange p0) <$> do
    case p of
      A.ConP i x as        -> return $ A.ConP        i x (as ++ ps)
      A.DefP i x as        -> return $ A.DefP        i x (as ++ ps)
      A.PatternSynP i x as -> return $ A.PatternSynP i x (as ++ ps)
      -- Dotted constructors are turned into "lazy" constructor patterns.
      A.DotP i (Ident x)   -> resolveName x >>= \case
        ConstructorName ds -> do
          let cpi = ConPatInfo ConOCon i ConPatLazy
              c   = AmbQ (fmap anameName ds)
          return $ A.ConP cpi c ps
        _ -> failure
      A.DotP{}    -> failure
      A.VarP{}    -> failure
      A.ProjP{}   -> failure
      A.WildP{}   -> failure
      A.AsP{}     -> failure
      A.AbsurdP{} -> failure
      A.LitP{}    -> failure
      A.RecP{}    -> failure
      A.EqualP{}  -> failure
      A.WithP{}   -> failure
  where
    failure = typeError $ InvalidPattern p0

instance ToAbstract C.Pattern (A.Pattern' C.Expr) where

    toAbstract (C.IdentP x) =
      resolvePatternIdentifier (getRange x) x Nothing

    toAbstract (AppP (QuoteP _) p)
      | IdentP x <- namedArg p,
        visible p = do
      e <- toAbstract (OldQName x Nothing)
      let quoted (A.Def x) = return x
          quoted (A.Macro x) = return x
          quoted (A.Proj _ p)
            | Just x <- getUnambiguous p = return x
            | otherwise                  = genericError $ "quote: Ambigous name: " ++ prettyShow (unAmbQ p)
          quoted (A.Con c)
            | Just x <- getUnambiguous c = return x
            | otherwise                  = genericError $ "quote: Ambigous name: " ++ prettyShow (unAmbQ c)
          quoted (A.ScopedExpr _ e) = quoted e
          quoted _                  = genericError $ "quote: not a defined name"
      A.LitP . LitQName (getRange x) <$> quoted e

    toAbstract (QuoteP r) =
      genericError "quote must be applied to an identifier"

    toAbstract p0@(AppP p q) = do
        reportSLn "scope.pat" 50 $ "distributeDots before = " ++ show p
        p <- distributeDots p
        reportSLn "scope.pat" 50 $ "distributeDots after  = " ++ show p
        (p', q') <- toAbstract (p, q)
        applyAPattern p0 p' [q']

        where
            distributeDots :: C.Pattern -> ScopeM C.Pattern
            distributeDots p@(C.DotP r e) = distributeDotsExpr r e
            distributeDots p = return p

            distributeDotsExpr :: Range -> C.Expr -> ScopeM C.Pattern
            distributeDotsExpr r e = parseRawApp e >>= \case
              C.App r e a     ->
                AppP <$> distributeDotsExpr r e
                     <*> (traverse . traverse) (distributeDotsExpr r) a
              OpApp r q ns as ->
                case (traverse . traverse . traverse) fromNoPlaceholder as of
                  Just as -> OpAppP r q ns <$>
                    (traverse . traverse . traverse) (distributeDotsExpr r) as
                  Nothing -> return $ C.DotP r e
              Paren r e -> ParenP r <$> distributeDotsExpr r e
              _ -> return $ C.DotP r e

            fromNoPlaceholder :: MaybePlaceholder (OpApp a) -> Maybe a
            fromNoPlaceholder (NoPlaceholder _ (Ordinary e)) = Just e
            fromNoPlaceholder _ = Nothing

            parseRawApp :: C.Expr -> ScopeM C.Expr
            parseRawApp (RawApp r es) = parseApplication es
            parseRawApp e             = return e

    toAbstract p0@(OpAppP r op ns ps) = do
        reportSLn "scope.pat" 60 $ "ConcreteToAbstract.toAbstract OpAppP{}: " ++ show p0
        p  <- resolvePatternIdentifier (getRange op) op (Just ns)
        ps <- toAbstract ps
        applyAPattern p0 p ps

    -- Removed when parsing
    toAbstract (HiddenP _ _)   = __IMPOSSIBLE__
    toAbstract (InstanceP _ _) = __IMPOSSIBLE__
    toAbstract (RawAppP _ _)   = __IMPOSSIBLE__
    toAbstract (EllipsisP _)   = __IMPOSSIBLE__

    toAbstract p@(C.WildP r)    = return $ A.WildP (PatRange r)
    -- Andreas, 2015-05-28 futile attempt to fix issue 819: repeated variable on lhs "_"
    -- toAbstract p@(C.WildP r)    = A.VarP <$> freshName r "_"
    toAbstract (C.ParenP _ p)   = toAbstract p
    toAbstract (C.LitP l)       = return $ A.LitP l
    toAbstract p0@(C.AsP r x p) = do
        -- Andreas, 2018-06-30, issue #3147: as-variables can be non-linear a priori!
        -- x <- toAbstract (NewName PatternBound x)
        x <- bindPatternVariable x
        p <- toAbstract p
        return $ A.AsP (PatRange r) (A.BindName x) p
    toAbstract p0@(C.EqualP r es)  = return $ A.EqualP (PatRange r) es

    -- We have to do dot patterns at the end since they can
    -- refer to the variables bound by the other patterns.
    toAbstract p0@(C.DotP r e) = do
      let fallback = return $ A.DotP (PatRange r) e
      case e of
        C.Ident x -> resolveName x >>= \case
          -- Andreas, 2018-06-19, #3130
          -- We interpret .x as postfix projection if x is a field name in scope
          FieldName xs -> return $ A.ProjP (PatRange r) ProjPostfix $ AmbQ $
            fmap anameName xs
          _ -> fallback
        _ -> fallback

    toAbstract p0@(C.AbsurdP r)    = return $ A.AbsurdP (PatRange r)
    toAbstract (C.RecP r fs)       = A.RecP (PatRange r) <$> mapM (traverse toAbstract) fs
    toAbstract (C.WithP r p)       = A.WithP (PatRange r) <$> toAbstract p

-- | An argument @OpApp C.Expr@ to an operator can have binders,
--   in case the operator is some @syntax@-notation.
--   For these binders, we have to create lambda-abstractions.
toAbstractOpArg :: Precedence -> OpApp C.Expr -> ScopeM A.Expr
toAbstractOpArg ctx (Ordinary e)                 = toAbstractCtx ctx e
toAbstractOpArg ctx (SyntaxBindingLambda r bs e) = toAbstractLam r bs e ctx

-- | Turn an operator application into abstract syntax. Make sure to
-- record the right precedences for the various arguments.
toAbstractOpApp :: C.QName -> Set A.Name ->
                   [NamedArg (MaybePlaceholder (OpApp C.Expr))] ->
                   ScopeM A.Expr
toAbstractOpApp op ns es = do
    -- Replace placeholders with bound variables.
    (binders, es) <- replacePlaceholders es
    -- Get the notation for the operator.
    nota <- getNotation op ns
    let parts = notation nota
    -- We can throw away the @BindingHoles@, since binders
    -- have been preprocessed into @OpApp C.Expr@.
    let nonBindingParts = filter (not . isBindingHole) parts
    -- We should be left with as many holes as we have been given args @es@.
    -- If not, crash.
    unless (length (filter isAHole nonBindingParts) == length es) __IMPOSSIBLE__
    -- Translate operator and its arguments (each in the right context).
    op <- toAbstract (OldQName op (Just ns))
    es <- left (notaFixity nota) nonBindingParts es
    -- Prepend the generated section binders (if any).
    let body = foldl' app op es
    return $ foldr (A.Lam (ExprRange (getRange body))) body binders
  where
    -- Build an application in the abstract syntax, with correct Range.
    app e (pref, arg) = A.App info e arg
      where info = (defaultAppInfo r) { appOrigin = getOrigin arg
                                      , appParens = pref }
            r = fuseRange e arg

    inferParenPref :: NamedArg (Either A.Expr (OpApp C.Expr)) -> ParenPreference
    inferParenPref e =
      case namedArg e of
        Right (Ordinary e) -> inferParenPreference e
        Left{}             -> PreferParenless  -- variable inserted by section expansion
        Right{}            -> PreferParenless  -- syntax lambda

    -- Translate an argument. Returns the paren preference for the argument, so
    -- we can build the correct info for the A.App node.
    toAbsOpArg :: Precedence ->
                  NamedArg (Either A.Expr (OpApp C.Expr)) ->
                  ScopeM (ParenPreference, NamedArg A.Expr)
    toAbsOpArg cxt e = (pref,) <$> (traverse . traverse) (either return (toAbstractOpArg cxt)) e
      where pref = inferParenPref e

    -- The hole left to the first @IdPart@ is filled with an expression in @LeftOperandCtx@.
    left f (IdPart _ : xs) es = inside f xs es
    left f (_ : xs) (e : es) = do
        e  <- toAbsOpArg (LeftOperandCtx f) e
        es <- inside f xs es
        return (e : es)
    left f (_  : _)  [] = __IMPOSSIBLE__
    left f []        _  = __IMPOSSIBLE__

    -- The holes in between the @IdPart@s is filled with an expression in @InsideOperandCtx@.
    inside f [x]          es    = right f x es
    inside f (IdPart _ : xs) es = inside f xs es
    inside f (_  : xs) (e : es) = do
        e  <- toAbsOpArg InsideOperandCtx e
        es <- inside f xs es
        return (e : es)
    inside _ (_ : _) [] = __IMPOSSIBLE__
    inside _ []         _  = __IMPOSSIBLE__

    -- The hole right of the last @IdPart@ is filled with an expression in @RightOperandCtx@.
    right _ (IdPart _)  [] = return []
    right f _          [e] = do
        let pref = inferParenPref e
        e <- toAbsOpArg (RightOperandCtx f pref) e
        return [e]
    right _ _     _  = __IMPOSSIBLE__

    replacePlaceholders ::
      [NamedArg (MaybePlaceholder (OpApp e))] ->
      ScopeM ([A.LamBinding], [NamedArg (Either A.Expr (OpApp e))])
    replacePlaceholders []       = return ([], [])
    replacePlaceholders (a : as) = case namedArg a of
      NoPlaceholder _ x -> mapSnd (set (Right x) a :) <$>
                             replacePlaceholders as
      Placeholder _     -> do
        x <- freshName noRange "section"
        let i = setOrigin Inserted $ argInfo a
        (ls, ns) <- replacePlaceholders as
        return ( A.DomainFree (unnamedArg i $ A.BindName x) : ls
               , set (Left (Var x)) a : ns
               )
      where
      set :: a -> NamedArg b -> NamedArg a
      set x arg = fmap (fmap (const x)) arg


{--------------------------------------------------------------------------
    Things we parse but are not part of the Agda file syntax
 --------------------------------------------------------------------------}

-- | Content of interaction hole.

instance ToAbstract C.HoleContent A.HoleContent where
  toAbstract = mapM toAbstract
