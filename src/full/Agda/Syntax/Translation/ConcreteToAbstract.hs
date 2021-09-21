
{-| Translation from "Agda.Syntax.Concrete" to "Agda.Syntax.Abstract". Involves scope analysis,
    figuring out infix operator precedences and tidying up definitions.
-}
module Agda.Syntax.Translation.ConcreteToAbstract
    ( ToAbstract(..), localToAbstract
    , concreteToAbstract_
    , concreteToAbstract
    , NewModuleQName(..)
    , TopLevel(..)
    , TopLevelInfo(..)
    , topLevelModuleName
    , AbstractRHS
    , NewModuleName, OldModuleName
    , NewName, OldQName
    , PatName, APatName
    , importPrimitives
    ) where

import Prelude hiding ( null )

import Control.Applicative hiding ( empty )
import Control.Monad.Except
import Control.Monad.Reader

import Data.Bifunctor
import Data.Foldable (traverse_)
import Data.Set (Set)
import Data.Map (Map)
import Data.Functor (void)
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid (First(..))
import Data.Void

import Agda.Syntax.Concrete as C hiding (topLevelModuleName)
import Agda.Syntax.Concrete.Generic
import Agda.Syntax.Concrete.Operators
import Agda.Syntax.Concrete.Pattern
import Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pattern as A ( patternVars, checkPatternLinearity, containsAsPattern, lhsCoreApp, lhsCoreWith )
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
import Agda.Syntax.Scope.Base as A
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Translation.AbstractToConcrete (ToConcrete, ConOfAbs)
import Agda.Syntax.DoNotation
import Agda.Syntax.IdiomBrackets

import Agda.TypeChecking.Monad.Base hiding (ModuleInfo, MetaInfo)
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Trace (traceCall, setCurrentRange)
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.MetaVars (registerInteractionPoint)
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Env (insideDotPattern, isInsideDotPattern, getCurrentPath)
import Agda.TypeChecking.Rules.Builtin (isUntypedBuiltin, bindUntypedBuiltin, builtinKindOfName)

import Agda.TypeChecking.Patterns.Abstract (expandPatternSynonyms)
import Agda.TypeChecking.Pretty hiding (pretty, prettyA)
import Agda.TypeChecking.Quote (quotedName)
import Agda.TypeChecking.Warnings

import Agda.Interaction.FindFile (checkModuleName, rootNameModule, SourceFile(SourceFile))
-- import Agda.Interaction.Imports  -- for type-checking in ghci
import {-# SOURCE #-} Agda.Interaction.Imports (scopeCheckImport)
import Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens
import Agda.Interaction.Options.Warnings

import qualified Agda.Utils.AssocList as AssocList
import Agda.Utils.CallStack ( HasCallStack, withCurrentCallStack )
import Agda.Utils.Char
import Agda.Utils.Either
import Agda.Utils.FileName
import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.List1 ( List1, pattern (:|) )
import Agda.Utils.List2 ( List2, pattern List2 )
import qualified Agda.Utils.List1 as List1
import qualified Agda.Utils.Map as Map
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Utils.Pretty as P
import Agda.Utils.Pretty (render, Pretty, pretty, prettyShow)
import Agda.Utils.Singleton
import Agda.Utils.Tuple

import Agda.Utils.Impossible
import Agda.ImpossibleTest (impossibleTest, impossibleTestReduceM)

{--------------------------------------------------------------------------
    Exceptions
 --------------------------------------------------------------------------}

notAnExpression :: (HasCallStack, MonadTCError m) => C.Expr -> m a
notAnExpression = locatedTypeError NotAnExpression

nothingAppliedToHiddenArg :: (HasCallStack, MonadTCError m) => C.Expr -> m a
nothingAppliedToHiddenArg = locatedTypeError NothingAppliedToHiddenArg

nothingAppliedToInstanceArg :: (HasCallStack, MonadTCError m) => C.Expr -> m a
nothingAppliedToInstanceArg = locatedTypeError NothingAppliedToInstanceArg

notAValidLetBinding :: (HasCallStack, MonadTCError m) => C.NiceDeclaration -> m a
notAValidLetBinding = locatedTypeError NotAValidLetBinding

{--------------------------------------------------------------------------
    Helpers
 --------------------------------------------------------------------------}
--UNUSED Liang-Ting Chen 2019-07-16
--annotateDecl :: ScopeM A.Declaration -> ScopeM A.Declaration
--annotateDecl m = annotateDecls $ (:[]) <$> m

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
    dot = \case
      A.VarP x               -> pure $ A.VarP x
      A.ConP i c args        -> A.ConP i c <$> (traverse $ traverse $ traverse dot) args
      A.ProjP i o d          -> pure $ A.ProjP i o d
      A.WildP i              -> pure $ A.WildP i
      A.AsP i x p            -> A.AsP i x <$> dot p
      A.DotP{}               -> genericError err
      A.EqualP{}             -> genericError err   -- Andrea: so we also disallow = patterns, reasonable?
      A.AbsurdP i            -> pure $ A.AbsurdP i
      A.LitP i l             -> pure $ A.LitP i l
      A.DefP i f args        -> A.DefP i f <$> (traverse $ traverse $ traverse dot) args
      A.PatternSynP i c args -> A.PatternSynP i c <$> (traverse $ traverse $ traverse dot) args
      A.RecP i fs            -> A.RecP i <$> (traverse $ traverse dot) fs
      A.WithP i p            -> A.WithP i <$> dot p
      A.AnnP i a p           -> genericError err   -- TODO: should this be allowed?
--UNUSED Liang-Ting Chen 2019-07-16
---- | Make sure that there are no dot patterns (WAS: called on pattern synonyms).
--noDotPattern :: String -> A.Pattern' e -> ScopeM (A.Pattern' Void)
--noDotPattern err = traverse $ const $ genericError err

newtype RecordConstructorType = RecordConstructorType [C.Declaration]

instance ToAbstract RecordConstructorType where
  type AbsOfCon RecordConstructorType = A.Expr
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
      -- TODO: Telescope instead of Expr in abstract RecDef
    buildType ds = do
      dummy <- A.Def . fromMaybe __IMPOSSIBLE__ <$> getBuiltinName' builtinSet
      tel   <- catMaybes <$> mapM makeBinding ds
      return $ A.mkPi (ExprRange (getRange ds)) tel dummy

    makeBinding :: C.NiceDeclaration -> ScopeM (Maybe A.TypedBinding)
    makeBinding d = do
      let failure = typeError $ NotValidBeforeField d
          r       = getRange d
          mkLet d = Just . A.TLet r <$> toAbstract (LetDef d)
      traceCall (SetRange r) $ case d of

        C.NiceField r pr ab inst tac x a -> do
          fx  <- getConcreteFixity x
          let bv = unnamed (C.mkBinder $ (C.mkBoundName x fx) { bnameTactic = tac }) <$ a
          toAbstract $ C.TBind r (singleton bv) (unArg a)

        -- Public open is allowed and will take effect when scope checking as
        -- proper declarations.
        C.NiceOpen r m dir -> do
          mkLet $ C.NiceOpen r m dir{ publicOpen = Nothing }
        C.NiceModuleMacro r p x modapp open dir -> do
          mkLet $ C.NiceModuleMacro r p x modapp open dir{ publicOpen = Nothing }

        -- Do some rudimentary matching here to get NotValidBeforeField instead
        -- of NotAValidLetDecl.
        C.NiceMutual _ _ _ _
          [ C.FunSig _ _ _ _ macro _ _ _ _ _
          , C.FunDef _ _ abstract _ _ _ _
             [ C.Clause _ _ (C.LHS _p [] []) (C.RHS _) NoWhere [] ]
          ] | abstract /= AbstractDef && macro /= MacroDef -> do
          mkLet d

        C.NiceLoneConstructor{} -> failure
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
    tel' <- catMaybes <$> toAbstract tel
    -- Scope check the old module name and the module args.
    m1    <- toAbstract $ OldModuleName m
    args' <- toAbstractCtx (ArgumentCtx PreferParen) args
    -- Copy the scope associated with m and take the parts actually imported.
    (adir, s) <- applyImportDirectiveM (C.QName x) dir' =<< getNamedScope m1
    (s', copyInfo) <- copyScope m m0 s
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
    (s', copyInfo) <- copyScope recN m0 s
    modifyCurrentScope $ const s'

    printScope "mod.inst" 20 "copied record module"
    return (A.RecordModuleInstance m1, copyInfo, adir)

-- | @checkModuleMacro mkApply range access concreteName modapp open dir@
--
--   Preserves local variables.

checkModuleMacro
  :: (ToConcrete a, Pretty (ConOfAbs a))
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
  -> ScopeM a
checkModuleMacro apply kind r p x modapp open dir = do
    reportSDoc "scope.decl" 70 $ vcat $
      [ text $ "scope checking ModuleMacro " ++ prettyShow x
      ]
    dir <- notPublicWithoutOpen open dir

    m0 <- toAbstract (NewModuleName x)
    reportSDoc "scope.decl" 90 $ "NewModuleName: m0 =" <+> prettyA m0

    printScope "mod.inst" 20 "module macro"

    -- If we're opening a /named/ module, the import directive is
    -- applied to the "open", otherwise to the module itself. However,
    -- "public" is always applied to the "open".
    let (moduleDir, openDir) = case (open, isNoName x) of
          (DoOpen,   False) -> (defaultImportDir, dir)
          (DoOpen,   True)  -> ( dir { publicOpen = Nothing }
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
    -- Andreas, 2014-09-02: @openModule@ might shadow some locals!
    adir <- case open of
      DontOpen -> return adir'
      DoOpen   -> do
        adir'' <- openModule kind (Just m0) (C.QName x) openDir
        -- Andreas, 2020-05-14, issue #4656
        -- Keep the more meaningful import directive for highlighting
        -- (the other one is a defaultImportDir).
        return $ if isNoName x then adir' else adir''

    printScope "mod.inst" 20 $ show open
    reportSDoc "scope.decl" 90 $ "after open   : m0 =" <+> prettyA m0

    stripNoNames
    printScope "mod.inst" 10 $ "after stripping"
    reportSDoc "scope.decl" 90 $ "after stripNo: m0 =" <+> prettyA m0

    let m      = m0 `withRangesOf` singleton x
        adecl  = apply info m modapp' copyInfo adir

    reportSDoc "scope.decl" 70 $ vcat $
      [ text $ "scope checked ModuleMacro " ++ prettyShow x
      ]
    reportSLn  "scope.decl" 90 $ "info    = " ++ show info
    reportSLn  "scope.decl" 90 $ "m       = " ++ prettyShow m
    reportSLn  "scope.decl" 90 $ "modapp' = " ++ show modapp'
    reportSDoc "scope.decl" 90 $ return $ pretty copyInfo
    reportSDoc "scope.decl" 70 $ nest 2 $ prettyA adecl
    return adecl
  where
    info = ModuleInfo
             { minfoRange  = r
             , minfoAsName = Nothing
             , minfoAsTo   = renamingRange dir
             , minfoOpenShort = Just open
             , minfoDirective = Just dir
             }

-- | The @public@ keyword must only be used together with @open@.

notPublicWithoutOpen :: OpenShortHand -> C.ImportDirective -> ScopeM C.ImportDirective
notPublicWithoutOpen DoOpen   dir = return dir
notPublicWithoutOpen DontOpen dir = do
  whenJust (publicOpen dir) $ \ r ->
    setCurrentRange r $ warning UselessPublic
  return $ dir { publicOpen = Nothing }

-- | Computes the range of all the \"to\" keywords used in a renaming
-- directive.

renamingRange :: C.ImportDirective -> Range
renamingRange = getRange . map renToRange . impRenaming

-- | Scope check a 'NiceOpen'.
checkOpen
  :: Range                -- ^ Range of @open@ statement.
  -> Maybe A.ModuleName   -- ^ Resolution of concrete module name (if already resolved).
  -> C.QName              -- ^ Module to open.
  -> C.ImportDirective    -- ^ Scope modifier.
  -> ScopeM (ModuleInfo, A.ModuleName, A.ImportDirective) -- ^ Arguments of 'A.Open'
checkOpen r mam x dir = do
  reportSDoc "scope.decl" 70 $ do
    cm <- getCurrentModule
    vcat $
      [ text   "scope checking NiceOpen " <> return (pretty x)
      , text   "  getCurrentModule       = " <> prettyA cm
      , text $ "  getCurrentModule (raw) = " ++ show cm
      , text $ "  C.ImportDirective      = " ++ prettyShow dir
      ]
  -- Andreas, 2017-01-01, issue #2377: warn about useless `public`
  whenJust (publicOpen dir) $ \ r -> do
    whenM ((A.noModuleName ==) <$> getCurrentModule) $ do
      setCurrentRange r $ warning UselessPublic

  m <- caseMaybe mam (toAbstract (OldModuleName x)) return
  printScope "open" 20 $ "opening " ++ prettyShow x
  adir <- openModule TopOpenModule (Just m) x dir
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
    text ( "scope checked NiceOpen " ++ prettyShow x
         ) : map (nest 2 . prettyA) adecls
  return (minfo, m, adir)

-- | Check a literal, issuing an error warning for bad literals.
checkLiteral :: Literal -> ScopeM ()
checkLiteral (LitChar c)
  | isSurrogateCodePoint c = genericNonFatalError $ P.text $ "Invalid character literal " ++ show c ++
                                                             " (surrogate code points are not supported)"
checkLiteral _ = return ()

{--------------------------------------------------------------------------
    Translation
 --------------------------------------------------------------------------}

concreteToAbstract_ :: ToAbstract c => c -> ScopeM (AbsOfCon c)
concreteToAbstract_ = toAbstract

concreteToAbstract :: ToAbstract c => ScopeInfo -> c -> ScopeM (AbsOfCon c)
concreteToAbstract scope x = withScope_ scope (toAbstract x)

-- | Things that can be translated to abstract syntax are instances of this
--   class.
class ToAbstract c where
    type AbsOfCon c
    toAbstract :: c -> ScopeM (AbsOfCon c)

-- | This function should be used instead of 'toAbstract' for things that need
--   to keep track of precedences to make sure that we don't forget about it.
toAbstractCtx :: ToAbstract c => Precedence -> c-> ScopeM (AbsOfCon c)
toAbstractCtx ctx c = withContextPrecedence ctx $ toAbstract c

--UNUSED Liang-Ting Chen 2019-07-16
--toAbstractTopCtx :: ToAbstract c a => c -> ScopeM a
--toAbstractTopCtx = toAbstractCtx TopCtx

toAbstractHiding :: (LensHiding h, ToAbstract c) => h -> c -> ScopeM (AbsOfCon c)
toAbstractHiding h | visible h = toAbstract -- don't change precedence if visible
toAbstractHiding _             = toAbstractCtx TopCtx

--UNUSED Liang-Ting Chen 2019-07-16
--setContextCPS :: Precedence -> (a -> ScopeM b) ->
--                 ((a -> ScopeM b) -> ScopeM b) -> ScopeM b
--setContextCPS p ret f = do
--  old <- useScope scopePrecedence
--  withContextPrecedence p $ f $ \ x -> setContextPrecedence old >> ret x
--
--localToAbstractCtx :: ToAbstract c =>
--                     Precedence -> c -> (AbsOfCon -> ScopeM (AbsOfCon c)) -> ScopeM (AbsOfCon c)
--localToAbstractCtx ctx c ret = setContextCPS ctx ret (localToAbstract c)

-- | This operation does not affect the scope, i.e. the original scope
--   is restored upon completion.
localToAbstract :: ToAbstract c => c -> (AbsOfCon c -> ScopeM b) -> ScopeM b
localToAbstract x ret = fst <$> localToAbstract' x ret

-- | Like 'localToAbstract' but returns the scope after the completion of the
--   second argument.
localToAbstract' :: ToAbstract c => c -> (AbsOfCon c -> ScopeM b) -> ScopeM (b, ScopeInfo)
localToAbstract' x ret = do
  scope <- getScope
  withScope scope $ ret =<< toAbstract x

instance ToAbstract () where
  type AbsOfCon () = ()
  toAbstract = pure

instance (ToAbstract c1, ToAbstract c2) => ToAbstract (c1, c2) where
  type AbsOfCon (c1, c2) = (AbsOfCon c1, AbsOfCon c2)
  toAbstract (x,y) = (,) <$> toAbstract x <*> toAbstract y

instance (ToAbstract c1, ToAbstract c2, ToAbstract c3) => ToAbstract (c1, c2, c3) where
  type AbsOfCon (c1, c2, c3) = (AbsOfCon c1, AbsOfCon c2, AbsOfCon c3)
  toAbstract (x,y,z) = flatten <$> toAbstract (x,(y,z))
    where
      flatten (x,(y,z)) = (x,y,z)

instance ToAbstract c => ToAbstract [c] where
  type AbsOfCon [c] = [AbsOfCon c]
  toAbstract = mapM toAbstract

instance ToAbstract c => ToAbstract (List1 c) where
  type AbsOfCon (List1 c) = List1 (AbsOfCon c)
  toAbstract = mapM toAbstract

instance (ToAbstract c1, ToAbstract c2) => ToAbstract (Either c1 c2) where
  type AbsOfCon (Either c1 c2) = Either (AbsOfCon c1) (AbsOfCon c2)
  toAbstract = traverseEither toAbstract toAbstract

instance ToAbstract c => ToAbstract (Maybe c) where
  type AbsOfCon (Maybe c) = Maybe (AbsOfCon c)
  toAbstract = traverse toAbstract

-- Names ------------------------------------------------------------------

data NewName a = NewName
  { newBinder   :: A.BindingSource -- what kind of binder?
  , newName     :: a
  } deriving (Functor)

data OldQName = OldQName
  C.QName              -- ^ Concrete name to be resolved
  (Maybe (Set A.Name)) -- ^ If a set is given, then the first name must
                       --   correspond to one of the names in the set.

-- | We sometimes do not want to fail hard if the name is not actually
--   in scope because we have a strategy to recover from this problem
--   (e.g. drop the offending COMPILE pragma)
data MaybeOldQName = MaybeOldQName OldQName

newtype OldName a = OldName a

-- | Wrapper to resolve a name to a 'ResolvedName' (rather than an 'A.Expr').
data ResolveQName = ResolveQName C.QName

data PatName      = PatName C.QName (Maybe (Set A.Name))
  -- ^ If a set is given, then the first name must correspond to one
  -- of the names in the set.

instance ToAbstract (NewName C.Name) where
  type AbsOfCon (NewName C.Name) = A.Name
  toAbstract (NewName b x) = do
    y <- freshAbstractName_ x
    bindVariable b x y
    return y

instance ToAbstract (NewName C.BoundName) where
  type AbsOfCon (NewName C.BoundName) = A.BindName
  toAbstract NewName{ newBinder = b, newName = BName{ boundName = x, bnameFixity = fx }} = do
    y <- freshAbstractName fx x
    bindVariable b x y
    return $ A.BindName y

instance ToAbstract OldQName where
  type AbsOfCon OldQName = A.Expr
  toAbstract q@(OldQName x _) =
    fromMaybeM (notInScopeError x) $ toAbstract (MaybeOldQName q)

instance ToAbstract MaybeOldQName where
  type AbsOfCon MaybeOldQName = Maybe A.Expr
  toAbstract (MaybeOldQName (OldQName x ns)) = do
    qx <- resolveName' allKindsOfNames ns x
    reportSLn "scope.name" 10 $ "resolved " ++ prettyShow x ++ ": " ++ prettyShow qx
    case qx of
      VarName x' _         -> return $ Just $ A.Var x'
      DefinedName _ d suffix -> do
        raiseWarningsOnUsage $ anameName d
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
        return $ withSuffix suffix $ nameToExpr d
        where
          withSuffix NoSuffix   e         = Just e
          withSuffix s@Suffix{} (A.Def x) = Just $ A.Def' x s
          withSuffix _          _         = Nothing

      FieldName     ds     -> ambiguous (A.Proj ProjPrefix) ds
      ConstructorName _ ds -> ambiguous A.Con ds
      PatternSynResName ds -> ambiguous A.PatternSyn ds
      UnknownName          -> pure Nothing
    where
      ambiguous :: (AmbiguousQName -> A.Expr) -> List1 AbstractName -> ScopeM (Maybe A.Expr)
      ambiguous f ds = do
        let xs = fmap anameName ds
        raiseWarningsOnUsageIfUnambiguous xs
        return $ Just $ f $ AmbQ xs

      -- Note: user warnings on ambiguous names will be raised by the type checker,
      -- see storeDiamsbiguatedName.
      raiseWarningsOnUsageIfUnambiguous :: List1 A.QName -> ScopeM ()
      raiseWarningsOnUsageIfUnambiguous = \case
        x :| [] -> raiseWarningsOnUsage x
        _       -> return ()


instance ToAbstract ResolveQName where
  type AbsOfCon ResolveQName = ResolvedName
  toAbstract (ResolveQName x) = resolveName x >>= \case
    UnknownName -> notInScopeError x
    q -> return q

data APatName = VarPatName A.Name
              | ConPatName (NonEmpty AbstractName)
              | PatternSynPatName (NonEmpty AbstractName)

instance ToAbstract PatName where
  type AbsOfCon PatName = APatName
  toAbstract (PatName x ns) = do
    reportSLn "scope.pat" 10 $ "checking pattern name: " ++ prettyShow x
    rx <- resolveName' (someKindsOfNames [ConName, CoConName, PatternSynName]) ns x
          -- Andreas, 2013-03-21 ignore conflicting names which cannot
          -- be meant since we are in a pattern
          -- Andreas, 2020-04-11 CoConName:
          -- coinductive constructors will be rejected later, in the type checker
    reportSLn "scope.pat" 20 $ "resolved as " ++ prettyShow rx
    case (rx, x) of
      (VarName y _,       C.QName x)                           -> bindPatVar x
      (FieldName d,       C.QName x)                           -> bindPatVar x
      (DefinedName _ d _, C.QName x) | isDefName (anameKind d) -> bindPatVar x
      (UnknownName,       C.QName x)                           -> bindPatVar x
      (ConstructorName _ ds, _)                                -> patCon ds
      (PatternSynResName d, _)                                 -> patSyn d
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
  y <- (AssocList.lookup x <$> getVarsToBind) >>= \case
    Just (LocalVar y _ _) -> do
      reportSLn "scope.pat" 10 $ "it was a old var: " ++ prettyShow x
      return $ setRange (getRange x) y
    Nothing -> do
      reportSLn "scope.pat" 10 $ "it was a new var: " ++ prettyShow x
      freshAbstractName_ x
  addVarToBind x $ LocalVar y PatternBound []
  return y

class ToQName a where
  toQName :: a -> C.QName

instance ToQName C.Name  where toQName = C.QName
instance ToQName C.QName where toQName = id

-- Should be a defined name.
instance ToQName a => ToAbstract (OldName a) where
  type AbsOfCon (OldName a) = A.QName
  toAbstract (OldName x) = do
    rx <- resolveName (toQName x)
    case rx of
      DefinedName _ d NoSuffix -> return $ anameName d
      DefinedName _ d Suffix{} -> notInScopeError (toQName x)
      -- We can get the cases below for DISPLAY pragmas
      ConstructorName _ ds -> return $ anameName (NonEmpty.head ds)   -- We'll throw out this one, so it doesn't matter which one we pick
      FieldName ds         -> return $ anameName (NonEmpty.head ds)
      PatternSynResName ds -> return $ anameName (NonEmpty.head ds)
      VarName x _          -> genericError $ "Not a defined name: " ++ prettyShow x
      UnknownName          -> notInScopeError (toQName x)

-- | Resolve a non-local name and return its possibly ambiguous abstract name.
toAbstractExistingName :: ToQName a => a -> ScopeM (List1 AbstractName)
toAbstractExistingName x = resolveName (toQName x) >>= \case
    DefinedName _ d NoSuffix -> return $ singleton d
    DefinedName _ d Suffix{} -> notInScopeError (toQName x)
    ConstructorName _ ds     -> return ds
    FieldName ds             -> return ds
    PatternSynResName ds     -> return ds
    VarName x _              -> genericError $ "Not a defined name: " ++ prettyShow x
    UnknownName              -> notInScopeError (toQName x)

newtype NewModuleName      = NewModuleName      C.Name
newtype NewModuleQName     = NewModuleQName     C.QName
newtype OldModuleName      = OldModuleName      C.QName

freshQModule :: A.ModuleName -> C.Name -> ScopeM A.ModuleName
freshQModule m x = A.qualifyM m . mnameFromList1 . singleton <$> freshAbstractName_ x

checkForModuleClash :: C.Name -> ScopeM ()
checkForModuleClash x = do
  ms :: [AbstractModule] <- scopeLookup (C.QName x) <$> getScope
  unless (null ms) $ do
    reportSLn "scope.clash" 20 $ "clashing modules ms = " ++ prettyShow ms
    reportSLn "scope.clash" 60 $ "clashing modules ms = " ++ show ms
    setCurrentRange x $
      typeError $ ShadowedModule x $
                map ((`withRangeOf` x) . amodName) ms

instance ToAbstract NewModuleName where
  type AbsOfCon NewModuleName = A.ModuleName
  toAbstract (NewModuleName x) = do
    checkForModuleClash x
    m <- getCurrentModule
    y <- freshQModule m x
    createModule Nothing y
    return y

instance ToAbstract NewModuleQName where
  type AbsOfCon NewModuleQName = A.ModuleName
  toAbstract (NewModuleQName m) = toAbs noModuleName m
    where
      toAbs m (C.QName x)  = do
        y <- freshQModule m x
        createModule Nothing y
        return y
      toAbs m (C.Qual x q) = do
        m' <- freshQModule m x
        toAbs m' q

instance ToAbstract OldModuleName where
  type AbsOfCon OldModuleName = A.ModuleName

  toAbstract (OldModuleName q) = setCurrentRange q $ do
    amodName <$> resolveModule q

-- Expressions ------------------------------------------------------------
--UNUSED Liang-Ting Chen 2019-07-16
---- | Peel off 'C.HiddenArg' and represent it as an 'NamedArg'.
--mkNamedArg :: C.Expr -> NamedArg C.Expr
--mkNamedArg (C.HiddenArg   _ e) = Arg (hide         defaultArgInfo) e
--mkNamedArg (C.InstanceArg _ e) = Arg (makeInstance defaultArgInfo) e
--mkNamedArg e                   = Arg defaultArgInfo $ unnamed e

-- | Peel off 'C.HiddenArg' and represent it as an 'Arg', throwing away any name.
mkArg' :: ArgInfo -> C.Expr -> Arg C.Expr
mkArg' info (C.HiddenArg   _ e) = Arg (hide         info) $ namedThing e
mkArg' info (C.InstanceArg _ e) = Arg (makeInstance info) $ namedThing e
mkArg' info e                   = Arg (setHiding NotHidden info) e
--UNUSED Liang-Ting 2019-07-16
---- | By default, arguments are @Relevant@.
--mkArg :: C.Expr -> Arg C.Expr
--mkArg e = mkArg' defaultArgInfo e

inferParenPreference :: C.Expr -> ParenPreference
inferParenPreference C.Paren{} = PreferParen
inferParenPreference _         = PreferParenless

-- | Parse a possibly dotted and braced @C.Expr@ as @A.Expr@,
--   interpreting dots as relevance and braces as hiding.
--   Only accept a layer of dotting/bracing if the respective accumulator is @Nothing@.
toAbstractDotHiding :: Maybe Relevance -> Maybe Hiding -> Precedence -> C.Expr -> ScopeM (A.Expr, Relevance, Hiding)
toAbstractDotHiding mr mh prec e = do
    reportSLn "scope.irrelevance" 100 $ "toAbstractDotHiding: " ++ render (pretty e)
    traceCall (ScopeCheckExpr e) $ case e of

      C.RawApp _ es     -> toAbstractDotHiding mr mh prec =<< parseApplication es
      C.Paren _ e       -> toAbstractDotHiding mr mh TopCtx e

      C.Dot _ e
        | Nothing <- mr -> toAbstractDotHiding (Just Irrelevant) mh prec e

      C.DoubleDot _ e
        | Nothing <- mr -> toAbstractDotHiding (Just NonStrict) mh prec e

      C.HiddenArg _ (Named Nothing e)
        | Nothing <- mh -> toAbstractDotHiding mr (Just Hidden) TopCtx e

      C.InstanceArg _ (Named Nothing e)
        | Nothing <- mh -> toAbstractDotHiding mr (Just $ Instance NoOverlap) TopCtx e

      e                 -> (, fromMaybe Relevant mr, fromMaybe NotHidden mh) <$>
                             toAbstractCtx prec e

-- | Translate concrete expression under at least one binder into nested
--   lambda abstraction in abstract syntax.
toAbstractLam :: Range -> List1 C.LamBinding -> C.Expr -> Precedence -> ScopeM A.Expr
toAbstractLam r bs e ctx = do
  -- Translate the binders
  lvars0 <- getLocalVars
  localToAbstract (fmap (C.DomainFull . makeDomainFull) bs) $ \ bs -> do
    lvars1 <- getLocalVars
    checkNoShadowing lvars0 lvars1
    -- Translate the body
    e <- toAbstractCtx ctx e
    -- We have at least one binder.  Get first @b@ and rest @bs@.
    return $ case List1.catMaybes bs of
      -- Andreas, 2020-06-18
      -- There is a pathological case in which we end up without binder:
      --   λ (let
      --        mutual -- warning: empty mutual block
      --     ) -> Set
      []   -> e
      b:bs -> A.Lam (ExprRange r) b $ foldr mkLam e bs
  where
    mkLam b e = A.Lam (ExprRange $ fuseRange b e) b e

-- | Scope check extended lambda expression.
scopeCheckExtendedLam ::
  Range -> Erased -> List1 C.LamClause -> ScopeM A.Expr
scopeCheckExtendedLam r erased cs = do
  whenM isInsideDotPattern $
    genericError "Extended lambdas are not allowed in dot patterns"

  -- Find an unused name for the extended lambda definition.
  cname <- freshConcreteName r 0 extendedLambdaName
  name  <- freshAbstractName_ cname
  a <- asksTC (^. lensIsAbstract)
  reportSDoc "scope.extendedLambda" 10 $ vcat
    [ text $ "new extended lambda name (" ++ show a ++ "): " ++ prettyShow name
    ]
  verboseS "scope.extendedLambda" 60 $ do
    forM_ cs $ \ c -> do
      reportSLn "scope.extendedLambda" 60 $ "extended lambda lhs: " ++ show (C.lamLHS c)
  qname <- qualifyName_ name
  bindName (PrivateAccess Inserted) FunName cname qname

  -- Andreas, 2019-08-20
  -- Keep the following __IMPOSSIBLE__, which is triggered by -v scope.decl.trace:80,
  -- for testing issue #4016.
  d <- C.FunDef r [] a NotInstanceDef __IMPOSSIBLE__ __IMPOSSIBLE__ cname . List1.toList <$> do
          forM cs $ \ (LamClause ps rhs ca) -> do
            let p   = C.rawAppP $ (killRange $ IdentP $ C.QName cname) :| ps
            let lhs = C.LHS p [] []
            return $ C.Clause cname ca lhs rhs NoWhere []
  scdef <- toAbstract d

  -- Create the abstract syntax for the extended lambda.
  case scdef of
    A.ScopedDecl si [A.FunDef di qname' NotDelayed cs] -> do
      setScope si  -- This turns into an A.ScopedExpr si $ A.ExtendedLam...
      return $
        A.ExtendedLam (ExprRange r) di erased qname' $
        List1.fromList cs
    _ -> __IMPOSSIBLE__

-- | Raise an error if argument is a C.Dot with Hiding info.

rejectPostfixProjectionWithHiding :: NamedArg C.Expr -> ScopeM ()
rejectPostfixProjectionWithHiding arg =
  case namedArg arg of
    C.Dot{} | notVisible arg -> setCurrentRange arg $ genericDocError $
      "Illegal hiding in postfix projection " P.<+> P.pretty arg
    _ -> return ()

-- | Scope check an expression.

instance ToAbstract C.Expr where
  type AbsOfCon C.Expr = A.Expr

  toAbstract e =
    traceCall (ScopeCheckExpr e) $ annotateExpr $ case e of

  -- Names
      Ident x -> toAbstract (OldQName x Nothing)

  -- Literals
      C.Lit r l -> do
        checkLiteral l
        case l of
          LitNat n -> do
            let builtin | n < 0     = Just <$> primFromNeg    -- negative literals are only allowed if FROMNEG is defined
                        | otherwise = ensureInScope =<< getBuiltin' builtinFromNat
            builtin >>= \case
              Just (I.Def q _) -> return $ mkApp q $ A.Lit i $ LitNat $ abs n
              _                -> return alit

          LitString s -> do
            getBuiltin' builtinFromString >>= ensureInScope >>= \case
              Just (I.Def q _) -> return $ mkApp q alit
              _                -> return alit

          _ -> return alit
        where
        i       = ExprRange r
        alit    = A.Lit i l
        mkApp q = A.App (defaultAppInfo r) (A.Def q) . defaultNamedArg

        -- #4925: Require fromNat/fromNeg to be in scope *unqualified* for literal overloading to
        -- apply.
        ensureInScope :: Maybe I.Term -> ScopeM (Maybe I.Term)
        ensureInScope v@(Just (I.Def q _)) =
          ifM (isNameInScopeUnqualified q <$> getScope) (return v) (return Nothing)
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
                    , metaNumber = __IMPOSSIBLE__ =<< n
                    , metaNameSuggestion = fromMaybe "" n
                    }

  -- Raw application
      C.RawApp r es -> do
        e <- parseApplication es
        toAbstract e

  -- Application
      C.App r e1 e2 -> do
        -- Andreas, 2021-02-10, issue #3289: reject @e {.p}@ and @e ⦃ .p ⦄@.
        rejectPostfixProjectionWithHiding e2

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
      C.ExtendedLam r e cs -> scopeCheckExtendedLam r e cs

  -- Relevant and irrelevant non-dependent function type
      C.Fun r (Arg info1 e1) e2 -> do
        let arg = mkArg' info1 e1
        let mr = case getRelevance arg of
              Relevant  -> Nothing
              r         -> Just r
        let mh = case getHiding arg of
              NotHidden -> Nothing
              h         -> Just h
        Arg info (e1', rel, hid) <- traverse (toAbstractDotHiding mr mh FunctionSpaceDomainCtx) arg
        let updRel = case rel of
              Relevant -> id
              rel      -> setRelevance rel
        let updHid = case hid of
              NotHidden -> id
              hid       -> setHiding hid
        A.Fun (ExprRange r) (Arg (updRel $ updHid info) e1') <$> toAbstractCtx TopCtx e2

  -- Dependent function type
      e0@(C.Pi tel e) -> do
        lvars0 <- getLocalVars
        localToAbstract tel $ \tel -> do
          lvars1 <- getLocalVars
          checkNoShadowing lvars0 lvars1
          e <- toAbstractCtx TopCtx e
          let info = ExprRange (getRange e0)
          return $ A.mkPi info (List1.catMaybes tel) e

  -- Let
      e0@(C.Let _ ds (Just e)) ->
        ifM isInsideDotPattern (genericError $ "Let-expressions are not allowed in dot patterns") $
        localToAbstract (LetDefs ds) $ \ds' -> do
          e <- toAbstractCtx TopCtx e
          let info = ExprRange (getRange e0)
          return $ A.mkLet info ds' e
      C.Let _ _ Nothing -> genericError "Missing body in let-expression"

  -- Record construction
      C.Rec r fs  -> do
        fs' <- toAbstractCtx TopCtx fs
        let ds'  = [ d | Right (_, Just d) <- fs' ]
            fs'' = map (mapRight fst) fs'
            i    = ExprRange r
        return $ A.mkLet i ds' (A.Rec i fs'')

  -- Record update
      C.RecUpdate r e fs -> do
        A.RecUpdate (ExprRange r) <$> toAbstract e <*> toAbstractCtx TopCtx fs

  -- Parenthesis
      C.Paren _ e -> toAbstractCtx TopCtx e

  -- Idiom brackets
      C.IdiomBrackets r es ->
        toAbstractCtx TopCtx =<< parseIdiomBracketsSeq r es

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
      C.DoubleDot _ _ -> genericError "Parse error: unexpected '..'"

  -- Quoting
      C.Quote r -> return $ A.Quote (ExprRange r)
      C.QuoteTerm r -> return $ A.QuoteTerm (ExprRange r)
      C.Unquote r -> return $ A.Unquote (ExprRange r)

      C.Tactic r e -> genericError "Syntax error: 'tactic' can only appear in attributes"

  -- DontCare
      C.DontCare e -> A.DontCare <$> toAbstract e

  -- forall-generalize
      C.Generalized e -> do
        (s, e) <- collectGeneralizables $ toAbstract e
        pure $ A.generalized s e

instance ToAbstract C.ModuleAssignment where
  type AbsOfCon C.ModuleAssignment = (A.ModuleName, Maybe A.LetBinding)
  toAbstract (C.ModuleAssignment m es i)
    | null es && isDefaultImportDir i = (, Nothing) <$> toAbstract (OldModuleName m)
    | otherwise = do
        x <- C.NoName (getRange m) <$> fresh
        r <- checkModuleMacro LetApply LetOpenModule (getRange (m, es, i)) PublicAccess x
               (C.SectionApp (getRange (m , es)) [] (rawApp (Ident m :| es)))
               DontOpen i
        case r of
          LetApply _ m' _ _ _ -> return (m', Just r)
          _ -> __IMPOSSIBLE__

instance ToAbstract c => ToAbstract (FieldAssignment' c) where
  type AbsOfCon (FieldAssignment' c) = FieldAssignment' (AbsOfCon c)

  toAbstract = traverse toAbstract

instance ToAbstract (C.Binder' (NewName C.BoundName)) where
  type AbsOfCon (C.Binder' (NewName C.BoundName)) = A.Binder

  toAbstract (C.Binder p n) = do
    let name = C.boundName $ newName n
    -- If we do have a pattern then the variable needs to be inserted
    -- so we do need a proper internal name for it.
    n <- if not (isNoName name && isJust p) then pure n else do
           n' <- freshConcreteName (getRange $ newName n) 0 patternInTeleName
           pure $ fmap (\ n -> n { C.boundName = n' }) n
    n <- toAbstract n
    -- Actually parsing the pattern, checking it is linear,
    -- and bind its variables
    p <- traverse parsePattern p
    p <- toAbstract p
    checkPatternLinearity p $ \ys ->
      typeError $ RepeatedVariablesInPattern ys
    bindVarsToBind
    p <- toAbstract p
    pure $ A.Binder p n

instance ToAbstract C.LamBinding where
  type AbsOfCon C.LamBinding = Maybe A.LamBinding

  toAbstract (C.DomainFree x)  = do
    tac <- traverse toAbstract $ bnameTactic $ C.binderName $ namedArg x
    Just . A.DomainFree tac <$> toAbstract (updateNamedArg (fmap $ NewName LambdaBound) x)
  toAbstract (C.DomainFull tb) = fmap A.DomainFull <$> toAbstract tb

makeDomainFull :: C.LamBinding -> C.TypedBinding
makeDomainFull (C.DomainFull b) = b
makeDomainFull (C.DomainFree x) = C.TBind r (singleton x) $ C.Underscore r Nothing
  where r = getRange x

instance ToAbstract C.TypedBinding where
  type AbsOfCon C.TypedBinding = Maybe A.TypedBinding

  toAbstract (C.TBind r xs t) = do
    t' <- toAbstractCtx TopCtx t
    tac <- traverse toAbstract $
             case List1.mapMaybe (bnameTactic . C.binderName . namedArg) xs of
               []      -> Nothing
               tac : _ -> Just tac
               -- Invariant: all tactics are the same
               -- (distributed in the parser, TODO: don't)
    xs' <- toAbstract $ fmap (updateNamedArg (fmap $ NewName LambdaBound)) xs
    return $ Just $ A.TBind r tac xs' t'
  toAbstract (C.TLet r ds) = A.mkTLet r <$> toAbstract (LetDefs ds)

-- | Scope check a module (top level function).
--
scopeCheckNiceModule
  :: Range
  -> Access
  -> C.Name
  -> C.Telescope
  -> ScopeM [A.Declaration]
  -> ScopeM A.Declaration
       -- ^ The returned declaration is an 'A.Section'.
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
      scopeCheckNiceModule noRange p noName_ [] $ singleton <$>
        scopeCheckNiceModule_ PublicAccess  -- See #4350

  | otherwise = do
        scopeCheckNiceModule_ p
  where
    -- The actual workhorse:
    scopeCheckNiceModule_ :: Access -> ScopeM A.Declaration
    scopeCheckNiceModule_ p = do

      -- Check whether we are dealing with an anonymous module.
      -- This corresponds to a Coq/LEGO section.
      (name, p', open) <- do
        if isNoName name then do
          (i :: NameId) <- fresh
          return (C.NoName (getRange name) i, PrivateAccess Inserted, True)
         else return (name, p, False)

      -- Check and bind the module, using the supplied check for its contents.
      aname <- toAbstract (NewModuleName name)
      d <- snd <$> do
        scopeCheckModule r (C.QName name) aname tel checkDs
      bindModule p' name aname

      -- If the module was anonymous open it public
      -- unless it's private, in which case we just open it (#2099)
      when open $
       void $ -- We can discard the returned default A.ImportDirective.
        openModule TopOpenModule (Just aname) (C.QName name) $
          defaultImportDir { publicOpen = boolToMaybe (p == PublicAccess) noRange }
      return d

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

  default ensureNoLetStms :: (Foldable t, EnsureNoLetStms b, t b ~ a) => a -> ScopeM ()
  ensureNoLetStms = traverse_ ensureNoLetStms

instance EnsureNoLetStms C.Binder where
  ensureNoLetStms arg@(C.Binder p n) =
    when (isJust p) $ typeError $ IllegalPatternInTelescope arg

instance EnsureNoLetStms C.TypedBinding where
  ensureNoLetStms = \case
    tb@C.TLet{}    -> typeError $ IllegalLetInTelescope tb
    C.TBind _ xs _ -> traverse_ (ensureNoLetStms . namedArg) xs

instance EnsureNoLetStms a => EnsureNoLetStms (LamBinding' a) where
  ensureNoLetStms = \case
    -- GA: DO NOT use traverse here: `LamBinding'` only uses its parameter in
    --     the DomainFull constructor so we would miss out on some potentially
    --     illegal lets! Cf. #4402
    C.DomainFree a -> ensureNoLetStms a
    C.DomainFull a -> ensureNoLetStms a

instance EnsureNoLetStms a => EnsureNoLetStms (Named_ a) where
instance EnsureNoLetStms a => EnsureNoLetStms (NamedArg a) where
instance EnsureNoLetStms a => EnsureNoLetStms [a] where


-- | Returns the scope inside the checked module.
scopeCheckModule
  :: Range                   -- ^ The range of the module.
  -> C.QName                 -- ^ The concrete name of the module.
  -> A.ModuleName            -- ^ The abstract name of the module.
  -> C.Telescope             -- ^ The module telescope.
  -> ScopeM [A.Declaration]  -- ^ The code for checking the module contents.
  -> ScopeM (ScopeInfo, A.Declaration)
       -- ^ The returned declaration is an 'A.Section'.
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
      return (scope, A.Section r (qm `withRangesOfQ` x) tel ds)

  -- Binding is done by the caller
  printScope "module" 20 $ "after module " ++ prettyShow x
  return res

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
topLevelModuleName = (^. scopeCurrent) . topLevelScope

-- | Top-level declarations are always
--   @
--     (import|open)*         -- a bunch of possibly opened imports
--     module ThisModule ...  -- the top-level module of this file
--   @
instance ToAbstract (TopLevel [C.Declaration]) where
    type AbsOfCon (TopLevel [C.Declaration]) = TopLevelInfo

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

                         -- GA #4888: We know we are in a bad place. But we still scopecheck
                         -- the initial segment on the off chance we generate a better error
                         -- message.
                         void importPrimitives
                         void $ toAbstract (Declarations outsideDecls)
                         void $ toAbstract (Declarations ds0)
                         -- Fail with a crude error otherwise
                         traceCall (SetRange $ getRange ds0) $ genericError
                           "Illegal declaration(s) before top-level module"

                    -- Otherwise, reconstruct the top-level module name
                    _ -> return $ C.QName $ setRange (getRange m0) $
                           C.simpleName $ stringToRawName $ rootNameModule file
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
                  checkModuleName (C.toTopLevelModuleName m0) (SourceFile file) $ Just expectedMName
                  return m0
          setTopLevelModule m
          am <- toAbstract (NewModuleQName m)
          primitiveImport <- importPrimitives
          -- Scope check the declarations outside
          outsideDecls <- toAbstract (Declarations outsideDecls)
          (insideScope, insideDecl) <- scopeCheckModule r m am tel $
             toAbstract (Declarations insideDecls)
          -- Andreas, 2020-05-13, issue #1804, #4647
          -- Do not eagerly remove private definitions, only when serializing
          -- let scope = over scopeModules (fmap $ restrictLocalPrivate am) insideScope
          let scope = insideScope
          setScope scope
          return $ TopLevelInfo (primitiveImport ++ outsideDecls ++ [ insideDecl ]) scope

        -- We already inserted the missing top-level module, see
        -- 'Agda.Syntax.Parser.Parser.figureOutTopLevelModule',
        -- thus, this case is impossible:
        _ -> __IMPOSSIBLE__

-- | Declaration @open import Agda.Primitive using (Set; Prop)@ when 'optImportSorts'.
importPrimitives :: ScopeM [A.Declaration]
importPrimitives = do
    noImportSorts <- not . optImportSorts <$> pragmaOptions
    -- Add implicit `open import Agda.Primitive using (Set; Prop)`
    let agdaPrimitiveName   = Qual (C.simpleName "Agda") $ C.QName $ C.simpleName "Primitive"
        agdaSetName         = C.simpleName "Set"
        agdaPropName        = C.simpleName "Prop"
        usingDirective      = Using [ImportedName agdaSetName, ImportedName agdaPropName]
        directives          = ImportDirective noRange usingDirective [] [] Nothing
        importAgdaPrimitive = [C.Import noRange agdaPrimitiveName Nothing C.DoOpen directives]
    if noImportSorts
      then return []
      else toAbstract (Declarations importAgdaPrimitive)

-- | runs Syntax.Concrete.Definitions.niceDeclarations on main module
niceDecls :: DoWarn -> [C.Declaration] -> ([NiceDeclaration] -> ScopeM a) -> ScopeM a
niceDecls warn ds ret = setCurrentRange ds $ computeFixitiesAndPolarities warn ds $ do
  fixs <- useScope scopeFixities  -- We need to pass the fixities to the nicifier for clause grouping
  let (result, warns') = runNice $ niceDeclarations fixs ds

  -- COMPILED pragmas are not allowed in safe mode unless we are in a builtin module.
  -- So we start by filtering out all the PragmaCompiled warnings if one of these two
  -- conditions is not met.
  isSafe    <- Lens.getSafeMode <$> pragmaOptions
  isBuiltin <- Lens.isBuiltinModule . filePath =<< getCurrentPath
  let warns = if isSafe && not isBuiltin then warns' else filter notOnlyInSafeMode warns'

  -- Respect the @DoWarn@ directive. For this to be sound, we need to know for
  -- sure that each @Declaration@ is checked at least once with @DoWarn@.
  unless (warn == NoWarn || null warns) $ do
    -- If there are some warnings and the --safe flag is set,
    -- we check that none of the NiceWarnings are fatal
    when isSafe $ do
      let (errs, ws) = List.partition unsafeDeclarationWarning warns
      -- If some of them are, we fail
      unless (null errs) $ do
        warnings $ NicifierIssue <$> ws
        tcerrs <- mapM warning_ $ NicifierIssue <$> errs
        setCurrentRange errs $ typeError $ NonFatalErrors tcerrs
    -- Otherwise we simply record the warnings
    mapM_ (\ w -> warning' (dwLocation w) $ NicifierIssue w) warns
  case result of
    Left (DeclarationException loc e) -> do
      reportSLn "error" 2 $ "Error raised at " ++ prettyShow loc
      throwError $ Exception (getRange e) $ pretty e
    Right ds -> ret ds

  where notOnlyInSafeMode = (PragmaCompiled_ /=) . declarationWarningName

-- | Wrapper to avoid instance conflict with generic list instance.
newtype Declarations = Declarations [C.Declaration]

instance ToAbstract Declarations where
  type AbsOfCon Declarations = [A.Declaration]

  toAbstract (Declarations ds) = do
    -- When --safe is active the termination checker (Issue 586),
    -- positivity checker (Issue 1614) and the coverage checker
    -- may not be switched off, and polarities may not be assigned.
    ds <- ifM (Lens.getSafeMode <$> pragmaOptions)
               {- then -} (mapM noUnsafePragma ds)
               {- else -} (return ds)

    niceDecls DoWarn ds toAbstract
   where

     -- We need to dig deep into a declaration, otherwise it is possible
     -- to hide an illegal pragma in a block. Cf. Issue #3983
     noUnsafePragma :: C.Declaration -> TCM C.Declaration
     noUnsafePragma = \case
       C.Pragma pr                 -> warnUnsafePragma pr
       C.RecordDef r n dir lams ds -> C.RecordDef r n dir lams <$> mapM noUnsafePragma ds
       C.Record r n dir lams e ds  -> C.Record r n dir lams e <$> mapM noUnsafePragma ds
       C.Mutual r ds               -> C.Mutual r <$> mapM noUnsafePragma ds
       C.Abstract r ds             -> C.Abstract r <$> mapM noUnsafePragma ds
       C.Private r o ds            -> C.Private r o <$> mapM noUnsafePragma ds
       C.InstanceB r ds            -> C.InstanceB r <$> mapM noUnsafePragma ds
       C.Macro r ds                -> C.Macro r <$> mapM noUnsafePragma ds
       d -> pure d

     warnUnsafePragma :: C.Pragma -> TCM C.Declaration
     warnUnsafePragma pr = C.Pragma pr <$ do
       ifM (Lens.isBuiltinModuleWithSafePostulates . filePath =<< getCurrentPath)
         {- then -} (pure ())
         {- else -} $ case unsafePragma pr of
         Nothing -> pure ()
         Just w  -> setCurrentRange pr $ warning w

     unsafePragma :: C.Pragma -> Maybe Warning
     unsafePragma = \case
       C.NoCoverageCheckPragma{}    -> Just SafeFlagNoCoverageCheck
       C.NoPositivityCheckPragma{}  -> Just SafeFlagNoPositivityCheck
       C.PolarityPragma{}           -> Just SafeFlagPolarity
       C.NoUniverseCheckPragma{}    -> Just SafeFlagNoUniverseCheck
       C.InjectivePragma{}          -> Just SafeFlagInjective
       C.TerminationCheckPragma _ m -> case m of
         NonTerminating       -> Just SafeFlagNonTerminating
         Terminating          -> Just SafeFlagTerminating
         TerminationCheck     -> Nothing
         TerminationMeasure{} -> Nothing
         -- ASR (31 December 2015). We don't pattern-match on
         -- @NoTerminationCheck@ because the @NO_TERMINATION_CHECK@ pragma
         -- was removed. See Issue #1763.
         NoTerminationCheck -> Nothing
       -- exhaustive match to get told by ghc we should have a look at this
       -- when we add new pragmas.
       C.OptionsPragma{}    -> Nothing
       C.BuiltinPragma{}    -> Nothing
       C.ForeignPragma{}    -> Nothing
       C.StaticPragma{}     -> Nothing
       C.InlinePragma{}     -> Nothing
       C.ImpossiblePragma{} -> Nothing
       C.EtaPragma{}        -> Just SafeFlagEta
       C.WarningOnUsage{}   -> Nothing
       C.WarningOnImport{}  -> Nothing
       C.DisplayPragma{}    -> Nothing
       C.CatchallPragma{}   -> Nothing
       -- @RewritePragma@ already requires --rewriting which is incompatible with --safe
       C.RewritePragma{}    -> Nothing
       -- @CompilePragma@ already handled in the nicifier
       C.CompilePragma{}    -> Nothing


newtype LetDefs = LetDefs (List1 C.Declaration)
newtype LetDef = LetDef NiceDeclaration

instance ToAbstract LetDefs where
  type AbsOfCon LetDefs = [A.LetBinding]

  toAbstract (LetDefs ds) =
    List1.concat <$> niceDecls DoWarn (List1.toList ds) (toAbstract . map LetDef)

instance ToAbstract LetDef where
  type AbsOfCon LetDef = List1 A.LetBinding
  toAbstract (LetDef d) =
    case d of
      NiceMutual _ _ _ _ d@[C.FunSig _ _ _ instanc macro info _ _ x t, C.FunDef _ _ abstract _ _ _ _ [cl]] ->
          do  when (abstract == AbstractDef) $ do
                genericError $ "`abstract` not allowed in let expressions"
              when (macro == MacroDef) $ do
                genericError $ "Macros cannot be defined in a let expression"
              t <- toAbstract t
              -- We bind the name here to make sure it's in scope for the LHS (#917).
              -- It's unbound for the RHS in letToAbstract.
              fx <- getConcreteFixity x
              x  <- A.unBind <$> toAbstract (NewName LetBound $ mkBoundName x fx)
              (x', e) <- letToAbstract cl
              -- If InstanceDef set info to Instance
              let info' = case instanc of
                    InstanceDef _  -> makeInstance info
                    NotInstanceDef -> info
              -- There are sometimes two instances of the
              -- let-bound variable, one declaration and one
              -- definition. The first list element below is
              -- used to highlight the declared instance in the
              -- right way (see Issue 1618).
              return $ A.LetDeclaredVariable (A.mkBindName (setRange (getRange x') x)) :|
                     [ A.LetBind (LetRange $ getRange d) info' (A.mkBindName x) t e
                     ]

      -- irrefutable let binding, like  (x , y) = rhs
      NiceFunClause r PublicAccess ConcreteDef tc cc catchall d@(C.FunClause lhs@(C.LHS p0 [] []) rhs0 wh ca) -> do
        noWhereInLetBinding wh
        rhs <- letBindingMustHaveRHS rhs0
        mp  <- setCurrentRange p0 $
                 (Right <$> parsePattern p0)
                   `catchError`
                 (return . Left)
        case mp of
          Right p -> do
            rhs <- toAbstract rhs
            setCurrentRange p0 $ do
              p   <- toAbstract p
              checkValidLetPattern p
              checkPatternLinearity p $ \ys ->
                typeError $ RepeatedVariablesInPattern ys
              bindVarsToBind
              p   <- toAbstract p
              return $ singleton $ A.LetPatBind (LetRange r) p rhs
          -- It's not a record pattern, so it should be a prefix left-hand side
          Left err ->
            case definedName p0 of
              Nothing -> throwError err
              Just x  -> toAbstract $ LetDef $ NiceMutual r tc cc YesPositivityCheck
                [ C.FunSig r PublicAccess ConcreteDef NotInstanceDef NotMacroDef (setOrigin Inserted defaultArgInfo) tc cc x (C.Underscore (getRange x) Nothing)
                , C.FunDef r __IMPOSSIBLE__ ConcreteDef NotInstanceDef __IMPOSSIBLE__ __IMPOSSIBLE__ __IMPOSSIBLE__
                  [C.Clause x (ca || catchall) lhs (C.RHS rhs) NoWhere []]
                ]
            where
              definedName (C.IdentP (C.QName x)) = Just x
              definedName C.IdentP{}             = Nothing
              definedName (C.RawAppP _ (List2 p _ _)) = definedName p
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
              definedName C.AppP{}               = Nothing -- Not impossible, see issue #4586
              definedName C.OpAppP{}             = __IMPOSSIBLE__
              definedName C.EllipsisP{}          = Nothing -- Not impossible, see issue #3937

      -- You can't open public in a let
      NiceOpen r x dirs -> do
        whenJust (publicOpen dirs) $ \r -> setCurrentRange r $ warning UselessPublic
        m    <- toAbstract (OldModuleName x)
        adir <- openModule_ LetOpenModule x dirs
        let minfo = ModuleInfo
              { minfoRange  = r
              , minfoAsName = Nothing
              , minfoAsTo   = renamingRange dirs
              , minfoOpenShort = Nothing
              , minfoDirective = Just dirs
              }
        return $ singleton $ A.LetOpen minfo m adir

      NiceModuleMacro r p x modapp open dir -> do
        whenJust (publicOpen dir) $ \ r -> setCurrentRange r $ warning UselessPublic
        -- Andreas, 2014-10-09, Issue 1299: module macros in lets need
        -- to be private
        singleton <$> checkModuleMacro LetApply LetOpenModule r (PrivateAccess Inserted) x modapp open dir

      _   -> notAValidLetBinding d
    where
        letToAbstract (C.Clause top _catchall (C.LHS p [] []) rhs0 wh []) = do
            noWhereInLetBinding wh
            rhs <- letBindingMustHaveRHS rhs0
            (x, args) <- do
              res <- setCurrentRange p $ parseLHS (C.QName top) p
              case res of
                C.LHSHead x args -> return (x, args)
                C.LHSProj{} -> genericError $ "Copatterns not allowed in let bindings"
                C.LHSWith{} -> genericError $ "`with` patterns not allowed in let bindings"
                C.LHSEllipsis{} -> genericError "`...` not allowed in let bindings"

            e <- localToAbstract args $ \args -> do
                bindVarsToBind
                -- Make sure to unbind the function name in the RHS, since lets are non-recursive.
                rhs <- unbindVariable top $ toAbstract rhs
                foldM lambda rhs (reverse args)  -- just reverse because these are DomainFree
            return (x, e)
        letToAbstract _ = notAValidLetBinding d

        -- Named patterns not allowed in let definitions
        lambda e (Arg info (Named Nothing (A.VarP x))) =
                return $ A.Lam i (A.mkDomainFree $ unnamedArg info $ A.mkBinder x) e
            where i = ExprRange (fuseRange x e)
        lambda e (Arg info (Named Nothing (A.WildP i))) =
            do  x <- freshNoName (getRange i)
                return $ A.Lam i' (A.mkDomainFree $ unnamedArg info $ A.mkBinder_ x) e
            where i' = ExprRange (fuseRange i e)
        lambda _ _ = notAValidLetBinding d

        noWhereInLetBinding :: C.WhereClause -> ScopeM ()
        noWhereInLetBinding = \case
          NoWhere -> return ()
          wh -> setCurrentRange wh $ genericError $ "`where` clauses not allowed in let bindings"
        letBindingMustHaveRHS :: C.RHS -> ScopeM C.Expr
        letBindingMustHaveRHS = \case
          C.RHS e -> return e
          C.AbsurdRHS -> genericError $ "Missing right hand side in let binding"

        -- Only record patterns allowed, but we do not exclude data constructors here.
        -- They will fail in the type checker.
        checkValidLetPattern :: A.Pattern' e -> ScopeM ()
        checkValidLetPattern = \case
            A.VarP{}             -> yes
            A.ConP _ _ ps        -> mapM_ (checkValidLetPattern . namedArg) ps
            A.ProjP{}            -> no
            A.DefP{}             -> no
            A.WildP{}            -> yes
            A.AsP _ _ p          -> checkValidLetPattern p
            A.DotP{}             -> no
            A.AbsurdP{}          -> no
            A.LitP{}             -> no
            A.PatternSynP _ _ ps -> mapM_ (checkValidLetPattern . namedArg) ps
            A.RecP _ fs          -> mapM_ (checkValidLetPattern . _exprFieldA) fs
            A.EqualP{}           -> no
            A.WithP{}            -> no
            A.AnnP _ _ p         -> checkValidLetPattern p
          where
          yes = return ()
          no  = genericError "Not a valid let pattern"


instance ToAbstract NiceDeclaration where
  type AbsOfCon NiceDeclaration = A.Declaration

  toAbstract d = annotateDecls $
    traceS "scope.decl.trace" 50
      [ "scope checking declaration"
      , "  " ++  prettyShow d
      ] $
    traceS "scope.decl.trace" 80  -- keep this debug message for testing issue #4016
      [ "scope checking declaration (raw)"
      , "  " ++  show d
      ] $
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
      whenM ((Lens.getSafeMode <$> commandLineOptions) `and2M`
             (not <$> (Lens.isBuiltinModuleWithSafePostulates . filePath =<< getCurrentPath)))
            (warning $ SafeFlagPostulate x)
      -- check the postulate
      singleton <$> toAbstractNiceAxiom AxiomName d

    C.NiceGeneralize r p i tac x t -> do
      reportSLn "scope.decl" 10 $ "found nice generalize: " ++ prettyShow x
      tac <- traverse (toAbstractCtx TopCtx) tac
      t_ <- toAbstractCtx TopCtx t
      let (s, t) = unGeneralized t_
      reportSLn "scope.decl" 50 $ "generalizations: " ++ show (Set.toList s, t)
      f <- getConcreteFixity x
      y <- freshAbstractQName f x
      bindName p GeneralizeName x y
      let info = (mkDefInfo x f p ConcreteDef r) { defTactic = tac }
      return [A.Generalize s info i y t]

  -- Fields
    C.NiceField r p a i tac x t -> do
      unless (p == PublicAccess) $ genericError "Record fields can not be private"
      -- Interaction points for record fields have already been introduced
      -- when checking the type of the record constructor.
      -- To avoid introducing interaction points (IP) twice, we turn
      -- all question marks to underscores.  (See issue 1138.)
      let maskIP (C.QuestionMark r _) = C.Underscore r Nothing
          maskIP e                     = e
      tac <- traverse (toAbstractCtx TopCtx) tac
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
      bindName p FldName x y
      let info = (mkDefInfoInstance x f p a i NotMacroDef r) { defTactic = tac }
      return [ A.Field info y t' ]

  -- Primitive function
    PrimitiveFunction r p a x t -> do
      t' <- traverse (toAbstractCtx TopCtx) t
      f  <- getConcreteFixity x
      y  <- freshAbstractQName f x
      bindName p PrimName x y
      return [ A.Primitive (mkDefInfo x f p a r) y t' ]

  -- Definitions (possibly mutual)
    NiceMutual r tc cc pc ds -> do
      ds' <- toAbstract ds
      -- We only termination check blocks that do not have a measure.
      return [ A.Mutual (MutualInfo tc cc pc r) ds' ]

    C.NiceRecSig r p a _pc _uc x ls t -> do
      ensureNoLetStms ls
      withLocalVars $ do
        (ls', _) <- withCheckNoShadowing $
          -- Minor hack: record types don't have indices so we include t when
          -- computing generalised parameters, but in the type checker any named
          -- generalizable arguments in the sort should be bound variables.
          toAbstract (GenTelAndType (map makeDomainFull ls) t)
        t' <- toAbstract t
        f  <- getConcreteFixity x
        x' <- freshAbstractQName f x
        bindName' p RecName (GeneralizedVarsMetadata $ generalizeTelVars ls') x x'
        return [ A.RecSig (mkDefInfo x f p a r) x' ls' t' ]

    C.NiceDataSig r p a pc uc x ls t -> do
        reportSLn "scope.data.sig" 20 ("checking DataSig for " ++ prettyShow x)
        ensureNoLetStms ls
        withLocalVars $ do
          ls' <- withCheckNoShadowing $
            toAbstract $ GenTel $ map makeDomainFull ls
          t'  <- toAbstract $ C.Generalized t
          f  <- getConcreteFixity x
          x' <- freshAbstractQName f x
          mErr <- bindName'' p DataName (GeneralizedVarsMetadata $ generalizeTelVars ls') x x'
          whenJust mErr $ \case
            err@(ClashingDefinition cn an _) -> do
              resolveName (C.QName x) >>= \case
                -- #4435: if a data type signature causes a ClashingDefinition error, and if
                -- the data type name is bound to an Axiom, then the error may be caused by
                -- the illegal type signature. Convert the NiceDataSig into a NiceDataDef
                -- (which removes the type signature) and suggest it as a possible fix.
                DefinedName p ax NoSuffix | anameKind ax == AxiomName -> do
                  let suggestion = NiceDataDef r Inserted a pc uc x ls []
                  typeError $ ClashingDefinition cn an (Just suggestion)
                _ -> typeError err
            otherErr -> typeError otherErr
          return [ A.DataSig (mkDefInfo x f p a r) x' ls' t' ]

  -- Type signatures
    C.FunSig r p a i m rel _ _ x t -> do
        let kind = if m == MacroDef then MacroName else FunName
        singleton <$> toAbstractNiceAxiom kind (C.Axiom r p a i rel x t)

  -- Function definitions
    C.FunDef r ds a i _ _ x cs -> do
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
    C.NiceFunClause _ _ _ _ _ _ (C.FunClause lhs _ _ _) ->
      genericError $
        "Missing type signature for left hand side " ++ prettyShow lhs
    C.NiceFunClause{} -> __IMPOSSIBLE__

  -- Data definitions
    C.NiceDataDef r o a _ uc x pars cons -> do
        reportSLn "scope.data.def" 20 ("checking " ++ show o ++ " DataDef for " ++ prettyShow x)
        (p, ax) <- resolveName (C.QName x) >>= \case
          DefinedName p ax NoSuffix -> do
            clashUnless x DataName ax  -- Andreas 2019-07-07, issue #3892
            livesInCurrentModule ax  -- Andreas, 2017-12-04, issue #2862
            clashIfModuleAlreadyDefinedInCurrentModule x ax
            return (p, ax)
          _ -> genericError $ "Missing type signature for data definition " ++ prettyShow x
        ensureNoLetStms pars
        withLocalVars $ do
          gvars <- bindGeneralizablesIfInserted o ax
          -- Check for duplicate constructors
          do cs <- mapM conName cons
             unlessNull (duplicates cs) $ \ dups -> do
               let bad = filter (`elem` dups) cs
               setCurrentRange bad $
                 typeError $ DuplicateConstructors dups

          pars <- catMaybes <$> toAbstract pars
          let x' = anameName ax
          -- Create the module for the qualified constructors
          checkForModuleClash x -- disallow shadowing previously defined modules
          let m = qnameToMName x'
          createModule (Just IsDataModule) m
          bindModule p x m  -- make it a proper module
          cons <- toAbstract (map (DataConstrDecl m a p) cons)
          printScope "data" 20 $ "Checked data " ++ prettyShow x
          f <- getConcreteFixity x
          return [ A.DataDef (mkDefInfo x f PublicAccess a r) x' uc (DataDefParams gvars pars) cons ]
      where
        conName (C.Axiom _ _ _ _ _ c _) = return c
        conName d = errorNotConstrDecl d

  -- Record definitions (mucho interesting)
    C.NiceRecDef r o a _ uc x (RecordDirectives ind eta pat cm) pars fields -> do
      reportSLn "scope.rec.def" 20 ("checking " ++ show o ++ " RecDef for " ++ prettyShow x)
      -- #3008: Termination pragmas are ignored in records
      checkNoTerminationPragma InRecordDef fields
      -- Andreas, 2020-04-19, issue #4560
      -- 'pattern' declaration is incompatible with 'coinductive' or 'eta-equality'.
      whenJust pat $ \ r -> do
        let warn = setCurrentRange r . warning . UselessPatternDeclarationForRecord
        if | Just (Ranged _ CoInductive) <- ind -> warn "coinductive"
           | Just YesEta                 <- eta -> warn "eta"
           | otherwise -> return ()

      (p, ax) <- resolveName (C.QName x) >>= \case
        DefinedName p ax NoSuffix -> do
          clashUnless x RecName ax  -- Andreas 2019-07-07, issue #3892
          livesInCurrentModule ax  -- Andreas, 2017-12-04, issue #2862
          clashIfModuleAlreadyDefinedInCurrentModule x ax
          return (p, ax)
        _ -> genericError $ "Missing type signature for record definition " ++ prettyShow x
      ensureNoLetStms pars
      withLocalVars $ do
        gvars <- bindGeneralizablesIfInserted o ax
        -- Check that the generated module doesn't clash with a previously
        -- defined module
        checkForModuleClash x
        pars   <- catMaybes <$> toAbstract pars
        let x' = anameName ax
        -- We scope check the fields a first time when putting together
        -- the type of the constructor.
        contel <- localToAbstract (RecordConstructorType fields) return
        m0     <- getCurrentModule
        let m = A.qualifyM m0 $ mnameFromList1 $ singleton $ List1.last $ qnameToList x'
        printScope "rec" 15 "before record"
        createModule (Just IsRecordModule) m
        -- We scope check the fields a second time, as actual fields.
        afields <- withCurrentModule m $ do
          afields <- toAbstract (Declarations fields)
          printScope "rec" 15 "checked fields"
          return afields
        -- Andreas, 2017-07-13 issue #2642 disallow duplicate fields
        -- Check for duplicate fields. (See "Check for duplicate constructors")
        do let fs :: [C.Name]
               fs = concat $ forMaybe fields $ \case
                 C.Field _ fs -> Just $ fs <&> \case
                   -- a Field block only contains field signatures
                   C.FieldSig _ _ f _ -> f
                   _ -> __IMPOSSIBLE__
                 _ -> Nothing
           unlessNull (duplicates fs) $ \ dups -> do
             let bad = filter (`elem` dups) fs
             setCurrentRange bad $
               typeError $ DuplicateFields dups
        bindModule p x m
        let kind = maybe ConName (conKindOfName . rangedThing) ind
        -- Andreas, 2019-11-11, issue #4189, no longer add record constructor to record module.
        cm' <- forM cm $ \ (c, _) -> bindRecordConstructorName c kind a p
        let inst = caseMaybe cm NotInstanceDef snd
        printScope "rec" 15 "record complete"
        f <- getConcreteFixity x
        let params = DataDefParams gvars pars
        let dir' = RecordDirectives ind eta pat cm'
        return [ A.RecDef (mkDefInfoInstance x f PublicAccess a inst NotMacroDef r) x' uc dir' params contel afields ]

    NiceModule r p a x@(C.QName name) tel ds -> do
      reportSDoc "scope.decl" 70 $ vcat $
        [ text $ "scope checking NiceModule " ++ prettyShow x
        ]

      adecl <- traceCall (ScopeCheckDeclaration $ NiceModule r p a x tel []) $ do
        scopeCheckNiceModule r p name tel $ toAbstract (Declarations ds)

      reportSDoc "scope.decl" 70 $ vcat $
        [ text $ "scope checked NiceModule " ++ prettyShow x
        , nest 2 $ prettyA adecl
        ]
      return [ adecl ]

    NiceModule _ _ _ m@C.Qual{} _ _ ->
      genericError $ "Local modules cannot have qualified names"

    NiceModuleMacro r p x modapp open dir -> do
      reportSDoc "scope.decl" 70 $ vcat $
        [ text $ "scope checking NiceModuleMacro " ++ prettyShow x
        ]

      adecl <- checkModuleMacro Apply TopOpenModule r p x modapp open dir

      reportSDoc "scope.decl" 70 $ vcat $
        [ text $ "scope checked NiceModuleMacro " ++ prettyShow x
        , nest 2 $ prettyA adecl
        ]
      return [ adecl ]

    NiceOpen r x dir -> do
      (minfo, m, adir) <- checkOpen r Nothing x dir
      return [A.Open minfo m adir]

    NicePragma r p -> do
      ps <- toAbstract p  -- could result in empty list of pragmas
      return $ map (A.Pragma r) ps

    NiceImport r x as open dir -> setCurrentRange r $ do
      dir <- notPublicWithoutOpen open dir

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
        Just (AsName (Left C.Underscore{})     r)         -> return $ Just $ AsName underscore r
        Just (AsName (Left (C.Ident C.Qual{})) r) -> illformedAs "; a qualified name is not allowed here"
        Just (AsName (Left e)                  r) -> illformedAs ""

      -- First scope check the imported module and return its name and
      -- interface. This is done with that module as the top-level module.
      -- This is quite subtle. We rely on the fact that when setting the
      -- top-level module and generating a fresh module name, the generated
      -- name will be exactly the same as the name generated when checking
      -- the imported module.
      (m, i) <- withCurrentModule noModuleName $ withTopLevelModule x $ do
        m <- toAbstract $ NewModuleQName x  -- (No longer erases the contents of @m@.)
        printScope "import" 10 "before import:"
        (m, i) <- scopeCheckImport m
        printScope "import" 10 $ "scope checked import: " ++ prettyShow i
        -- We don't want the top scope of the imported module (things happening
        -- before the module declaration)
        return (m, Map.delete noModuleName i)

      -- Bind the desired module name to the right abstract name.
      (name, theAsSymbol, theAsName) <- case as of

         Just a | let y = asName a, not (isNoName y) -> do
           bindModule (PrivateAccess Inserted) y m
           return (C.QName y, asRange a, Just y)

         _ -> do
           -- Don't bind if @import ... as _@ with "no name"
           whenNothing as $ bindQModule (PrivateAccess Inserted) x m
           return (x, noRange, Nothing)

      -- Open if specified, otherwise apply import directives
      adir <- case open of

        -- With @open@ import directives apply to the opening.
        -- The module is thus present in its qualified form without restrictions.
        DoOpen   -> do

          -- Merge the imported scopes with the current scopes.
          -- This might override a previous import of @m@, but monotonously (add stuff).
          modifyScopes $ \ ms -> Map.unionWith mergeScope (Map.delete m ms) i

          -- Andreas, 2019-05-29, issue #3818.
          -- Pass the resolved name to open instead triggering another resolution.
          -- This helps in situations like
          -- @
          --    module Top where
          --    module M where
          --    open import M
          -- @
          -- It is clear than in @open import M@, name @M@ must refer to a file
          -- rather than the above defined local module @M@.
          -- This already worked in the situation
          -- @
          --    module Top where
          --    module M where
          --    import M
          -- @
          -- Note that the manual desugaring of @open import@ as
          -- @
          --    module Top where
          --    module M where
          --    import M
          --    open M
          -- @
          -- will not work, as @M@ is now ambiguous in @open M@;
          -- the information that @M@ is external is lost here.
          (_minfo, _m, adir) <- checkOpen r (Just m) name dir
          return adir

        -- If not opening, import directives are applied to the original scope.
        DontOpen -> do
          (adir, i') <- Map.adjustM' (applyImportDirectiveM x dir) m i
          -- Andreas, 2020-05-18, issue #3933
          -- We merge the new imports without deleting old imports, to be monotone.
          modifyScopes $ \ ms -> Map.unionWith mergeScope ms i'
          return adir

      printScope "import" 10 "merged imported sig:"
      let minfo = ModuleInfo
            { minfoRange     = r
            , minfoAsName    = theAsName
            , minfoAsTo      = getRange (theAsSymbol, renamingRange dir)
            , minfoOpenShort = Just open
            , minfoDirective = Just dir
            }
      return [ A.Import minfo m adir ]

    NiceUnquoteDecl r p a i tc cc xs e -> do
      fxs <- mapM getConcreteFixity xs
      ys <- zipWithM freshAbstractQName fxs xs
      zipWithM_ (bindName p QuotableName) xs ys
      e <- toAbstract e
      zipWithM_ (rebindName p OtherDefName) xs ys
      let mi = MutualInfo tc cc YesPositivityCheck r
      return [ A.Mutual mi [A.UnquoteDecl mi [ mkDefInfoInstance x fx p a i NotMacroDef r | (fx, x) <- zip fxs xs ] ys e] ]

    NiceUnquoteDef r p a _ _ xs e -> do
      fxs <- mapM getConcreteFixity xs
      ys <- mapM (toAbstract . OldName) xs
      zipWithM_ (rebindName p QuotableName) xs ys
      e <- toAbstract e
      zipWithM_ (rebindName p OtherDefName) xs ys
      return [ A.UnquoteDef [ mkDefInfo x fx PublicAccess a r | (fx, x) <- zip fxs xs ] ys e ]

    NicePatternSyn r a n as p -> do
      reportSLn "scope.pat" 10 $ "found nice pattern syn: " ++ prettyShow n
      (as, p) <- withLocalVars $ do
         p  <- toAbstract =<< parsePatternSyn p
         when (containsAsPattern p) $
           typeError $ GenericError $
             "@-patterns are not allowed in pattern synonyms"
         checkPatternLinearity p $ \ys ->
           typeError $ RepeatedVariablesInPattern ys
         bindVarsToBind
         let err = "Dot or equality patterns are not allowed in pattern synonyms. Maybe use '_' instead."
         p <- noDotorEqPattern err p
         as <- (traverse . mapM) (unVarName <=< resolveName . C.QName) as
         unlessNull (patternVars p List.\\ map unArg as) $ \ xs -> do
           typeError . GenericDocError =<< do
             "Unbound variables in pattern synonym: " <+>
               sep (map prettyA xs)
         return (as, p)
      y <- freshAbstractQName' n
      bindName a PatternSynName n y
      -- Expanding pattern synonyms already at definition makes it easier to
      -- fold them back when printing (issue #2762).
      ep <- expandPatternSynonyms p
      modifyPatternSyns (Map.insert y (as, ep))
      return [A.PatternSynDef y (map (fmap BindName) as) p]   -- only for highlighting, so use unexpanded version
      where unVarName (VarName a _) = return a
            unVarName _ = typeError $ UnusedVariableInPatternSynonym

    d@NiceLoneConstructor{} -> withCurrentCallStack $ \ stk -> do
      warning $ NicifierIssue (DeclarationWarning stk (InvalidConstructorBlock (getRange d)))
      pure []

    where
      -- checking postulate or type sig. without checking safe flag
      toAbstractNiceAxiom :: KindOfName -> C.NiceDeclaration -> ScopeM A.Declaration
      toAbstractNiceAxiom kind (C.Axiom r p a i info x t) = do
        t' <- toAbstractCtx TopCtx t
        f  <- getConcreteFixity x
        mp <- getConcretePolarity x
        y  <- freshAbstractQName f x
        let isMacro | kind == MacroName = MacroDef
                    | otherwise         = NotMacroDef
        bindName p kind x y
        return $ A.Axiom kind (mkDefInfoInstance x f p a i isMacro r) info mp y t'
      toAbstractNiceAxiom _ _ = __IMPOSSIBLE__

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
  fvBefore <- length <$> getLocalVars
  (s, res) <- collectGeneralizables m
  fvAfter  <- length <$> getLocalVars
  -- We should bind the named generalizable variables as fresh variables
  binds <- createBoundNamesForGeneralizables s
  -- Issue #3735: We need to bind the generalizable variables outside any variables bound by `m`.
  outsideLocalVars (fvAfter - fvBefore) $ bindGeneralizables binds
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

instance ToAbstract GenTel where
  type AbsOfCon GenTel = A.GeneralizeTelescope
  toAbstract (GenTel tel) =
    uncurry A.GeneralizeTel <$> collectAndBindGeneralizables (catMaybes <$> toAbstract tel)

instance ToAbstract GenTelAndType where
  type AbsOfCon GenTelAndType = (A.GeneralizeTelescope, A.Expr)

  toAbstract (GenTelAndType tel t) = do
    (binds, (tel, t)) <- collectAndBindGeneralizables $
                          (,) <$> toAbstract tel <*> toAbstract t
    return (A.GeneralizeTel binds (catMaybes tel), t)

-- | Make sure definition is in same module as signature.
class LivesInCurrentModule a where
  livesInCurrentModule :: a -> ScopeM ()

instance LivesInCurrentModule AbstractName where
  livesInCurrentModule = livesInCurrentModule . anameName

instance LivesInCurrentModule A.QName where
  livesInCurrentModule x = do
    m <- getCurrentModule
    reportS "scope.data.def" 30
      [ "  A.QName of data type: " ++ prettyShow x
      , "  current module: " ++ prettyShow m
      ]
    unless (A.qnameModule x == m) $
      genericError $ "Definition in different module than its type signature"

-- | Unless the resolved 'AbstractName' has the given 'KindOfName',
--   report a 'ClashingDefinition' for the 'C.Name'.
clashUnless :: C.Name -> KindOfName -> AbstractName -> ScopeM ()
clashUnless x k ax = unless (anameKind ax == k) $
  typeError $ ClashingDefinition (C.QName x) (anameName ax) Nothing

-- | If a (data/record) module with the given name is already present in the current module,
--   we take this as evidence that a data/record with that name is already defined.
clashIfModuleAlreadyDefinedInCurrentModule :: C.Name -> AbstractName -> ScopeM ()
clashIfModuleAlreadyDefinedInCurrentModule x ax = do
  datRecMods <- catMaybes <$> do
    mapM (isDatatypeModule . amodName) =<< lookupModuleInCurrentModule x
  unlessNull datRecMods $ const $
    typeError $ ClashingDefinition (C.QName x) (anameName ax) Nothing

lookupModuleInCurrentModule :: C.Name -> ScopeM [AbstractModule]
lookupModuleInCurrentModule x =
  fromMaybe [] . Map.lookup x . nsModules . thingsInScope [PublicNS, PrivateNS] <$> getCurrentScope

data DataConstrDecl = DataConstrDecl A.ModuleName IsAbstract Access C.NiceDeclaration

-- | Bind a @data@ constructor.
bindConstructorName
  :: ModuleName      -- ^ Name of @data@/@record@ module.
  -> C.Name          -- ^ Constructor name.
  -> IsAbstract
  -> Access
  -> ScopeM A.QName
bindConstructorName m x a p = do
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
    p'' = case a of
            AbstractDef -> PrivateAccess Inserted
            _           -> PublicAccess

-- | Record constructors do not live in the record module (as it is parameterized).
--   Abstract constructors are bound privately, so that they are not exported.
bindRecordConstructorName :: C.Name -> KindOfName -> IsAbstract -> Access -> ScopeM A.QName
bindRecordConstructorName x kind a p = do
  y <- freshAbstractQName' x
  bindName p' kind x y
  return y
  where
    -- An abstract constructor is private (abstract constructor means
    -- abstract datatype, so the constructor should not be exported).
    p' = case a of
           AbstractDef -> PrivateAccess Inserted
           _           -> p

instance ToAbstract DataConstrDecl where
  type AbsOfCon DataConstrDecl = A.Declaration

  toAbstract (DataConstrDecl m a p d) = do
    case d of
      C.Axiom r p1 a1 i info x t -> do -- rel==Relevant
        -- unless (p1 == p) __IMPOSSIBLE__  -- This invariant is currently violated by test/Succeed/Issue282.agda
        unless (a1 == a) __IMPOSSIBLE__
        t' <- toAbstractCtx TopCtx t
        -- The abstract name is the qualified one
        -- Bind it twice, once unqualified and once qualified
        f <- getConcreteFixity x
        y <- bindConstructorName m x a p
        printScope "con" 15 "bound constructor"
        return $ A.Axiom ConName (mkDefInfoInstance x f p a i NotMacroDef r)
                         info Nothing y t'
      _ -> errorNotConstrDecl d

errorNotConstrDecl :: C.NiceDeclaration -> ScopeM a
errorNotConstrDecl d = typeError . GenericDocError $
        "Illegal declaration in data type definition " P.$$
        P.nest 2 (P.vcat $ map pretty (notSoNiceDeclarations d))

instance ToAbstract C.Pragma where
  type AbsOfCon C.Pragma = [A.Pragma]

  toAbstract (C.ImpossiblePragma _ strs) =
    case strs of
      "ReduceM" : _ -> impossibleTestReduceM strs
      _ -> impossibleTest strs
  toAbstract (C.OptionsPragma _ opts) = return [ A.OptionsPragma opts ]
  toAbstract (C.RewritePragma _ _ []) = [] <$ warning EmptyRewritePragma
  toAbstract (C.RewritePragma _ r xs) = singleton . A.RewritePragma r . concat <$> do
   forM xs $ \ x -> do
    e <- toAbstract $ OldQName x Nothing
    case e of
      A.Def x          -> return [ x ]
      A.Proj _ p | Just x <- getUnambiguous p -> return [ x ]
      A.Proj _ x       -> genericError $ "REWRITE used on ambiguous name " ++ prettyShow x
      A.Con c | Just x <- getUnambiguous c -> return [ x ]
      A.Con x          -> genericError $ "REWRITE used on ambiguous name " ++ prettyShow x
      A.Var x          -> genericError $ "REWRITE used on parameter " ++ prettyShow x ++ " instead of on a defined symbol"
      _       -> __IMPOSSIBLE__
  toAbstract (C.ForeignPragma _ rb s) = [] <$ addForeignCode (rangedThing rb) s
  toAbstract (C.CompilePragma _ rb x s) = do
    me <- toAbstract $ MaybeOldQName $ OldQName x Nothing
    case me of
      Nothing -> [] <$ notInScopeWarning x
      Just e  -> do
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
        return [ A.CompilePragma rb y s ]

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
  toAbstract (C.BuiltinPragma _ rb qx)
    | isUntypedBuiltin b = do
        q <- toAbstract $ ResolveQName qx
        bindUntypedBuiltin b q
        return [ A.BuiltinPragma rb q ]
        -- Andreas, 2015-02-14
        -- Some builtins cannot be given a valid Agda type,
        -- thus, they do not come with accompanying postulate or definition.
    | isBuiltinNoDef b = do
          case qx of
            C.QName x -> do
              -- The name shouldn't exist yet. If it does, we raise a warning
              -- and drop the existing definition.
              unlessM ((UnknownName ==) <$> resolveName qx) $ do
                genericWarning $ P.text $
                   "BUILTIN " ++ b ++ " declares an identifier " ++
                   "(no longer expects an already defined identifier)"
                modifyCurrentScope $ removeNameFromScope PublicNS x
              -- We then happily bind the name
              y <- freshAbstractQName' x
              let kind = fromMaybe __IMPOSSIBLE__ $ builtinKindOfName b
              bindName PublicAccess kind x y
              return [ A.BuiltinNoDefPragma rb kind y ]
            _ -> genericError $
              "Pragma BUILTIN " ++ b ++ ": expected unqualified identifier, " ++
              "but found " ++ prettyShow qx
    | otherwise = do
          q0 <- toAbstract $ ResolveQName qx

          -- Andreas, 2020-04-12, pr #4574.  For highlighting purposes:
          -- Rebind 'BuiltinPrim' as 'PrimName' and similar.
          q <- case (q0, builtinKindOfName b, qx) of
            (DefinedName acc y suffix, Just kind, C.QName x)
              | anameKind y /= kind
              , kind `elem` [ PrimName, AxiomName ] -> do
                  rebindName acc kind x $ anameName y
                  return $ DefinedName acc y{ anameKind = kind } suffix
            _ -> return q0

          return [ A.BuiltinPragma rb q ]
    where b = rangedThing rb

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
        getHead (C.RawAppP _ (List2 p _ _)) = getHead p
        getHead _                     = err

    top <- getHead lhs

    (isPatSyn, hd) <- do
      qx <- resolveName' allKindsOfNames Nothing top
      case qx of
        VarName x' _                -> return . (False,) $ A.qnameFromList $ singleton x'
        DefinedName _ d NoSuffix    -> return . (False,) $ anameName d
        DefinedName _ d Suffix{}    -> genericError $ "Invalid pattern " ++ prettyShow top
        FieldName     (d :| [])     -> return . (False,) $ anameName d
        FieldName ds                -> genericError $ "Ambiguous projection " ++ prettyShow top ++ ": " ++ prettyShow (fmap anameName ds)
        ConstructorName _ (d :| []) -> return . (False,) $ anameName d
        ConstructorName _ ds        -> genericError $ "Ambiguous constructor " ++ prettyShow top ++ ": " ++ prettyShow (fmap anameName ds)
        UnknownName                 -> notInScopeError top
        PatternSynResName (d :| []) -> return . (True,) $ anameName d
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

  -- A warning attached to an ambiguous name shall apply to all disambiguations.
  toAbstract (C.WarningOnUsage _ x str) = do
    ys <- fmap anameName <$> toAbstractExistingName x
    forM_ ys $ \ qn -> stLocalUserWarnings `modifyTCLens` Map.insert qn str
    return []

  toAbstract (C.WarningOnImport _ str) = do
    stWarningOnImport `setTCLens` Just str
    pure []

  -- Termination, Coverage, Positivity, Universe, and Catchall
  -- pragmes are handled by the nicifier
  toAbstract C.TerminationCheckPragma{}  = __IMPOSSIBLE__
  toAbstract C.NoCoverageCheckPragma{}   = __IMPOSSIBLE__
  toAbstract C.NoPositivityCheckPragma{} = __IMPOSSIBLE__
  toAbstract C.NoUniverseCheckPragma{}   = __IMPOSSIBLE__
  toAbstract C.CatchallPragma{}          = __IMPOSSIBLE__

  -- Polarity pragmas are handled by the niceifier.
  toAbstract C.PolarityPragma{} = __IMPOSSIBLE__

instance ToAbstract C.Clause where
  type AbsOfCon C.Clause = A.Clause

  toAbstract (C.Clause top catchall lhs@(C.LHS p eqs with) rhs wh wcs) = withLocalVars $ do
    -- Jesper, 2018-12-10, #3095: pattern variables bound outside the
    -- module are locally treated as module parameters
    modifyScope_ $ updateScopeLocals $ map $ second patternToModuleBound
    -- Andreas, 2012-02-14: need to reset local vars before checking subclauses
    vars0 <- getLocalVars
    lhs' <- toAbstract $ LeftHandSide (C.QName top) p
    printLocals 10 "after lhs:"
    vars1 <- getLocalVars
    eqs <- mapM (toAbstractCtx TopCtx) eqs
    vars2 <- getLocalVars
    let vars = dropEnd (length vars1) vars2 ++ vars0
    let wcs' = (vars, wcs)

    -- Handle rewrite equations first.
    if not (null eqs)
      then do
        rhs <- toAbstractCtx TopCtx $ RightHandSide eqs with wcs' rhs wh
        rhs <- toAbstract rhs
        return $ A.Clause lhs' [] rhs A.noWhereDecls catchall
      else do
        -- the right hand side is checked with the module of the local definitions opened
        (rhs, ds) <- whereToAbstract (getRange wh) wh $
                       toAbstractCtx TopCtx $ RightHandSide [] with wcs' rhs NoWhere
        rhs <- toAbstract rhs
        return $ A.Clause lhs' [] rhs ds catchall


whereToAbstract
  :: Range                            -- ^ The range of the @where@ block.
  -> C.WhereClause                    -- ^ The @where@ block.
  -> ScopeM a                         -- ^ The scope-checking task to be run in the context of the @where@ module.
  -> ScopeM (a, A.WhereDeclarations)  -- ^ Additionally return the scope-checked contents of the @where@ module.
whereToAbstract r wh inner = do
  case wh of
    NoWhere       -> ret
    AnyWhere _ [] -> warnEmptyWhere
    AnyWhere _ ds -> do
      -- Andreas, 2016-07-17 issues #2081 and #2101
      -- where-declarations are automatically private.
      -- This allows their type signature to be checked InAbstractMode.
      whereToAbstract1 r Nothing (singleton $ C.Private noRange Inserted ds) inner
    SomeWhere _ m a ds0 -> List1.ifNull ds0 warnEmptyWhere {-else-} $ \ ds -> do
      -- Named where-modules do not default to private.
      whereToAbstract1 r (Just (m, a)) ds inner
  where
  ret = (,A.noWhereDecls) <$> inner
  warnEmptyWhere = do
    setCurrentRange r $ warning EmptyWhere
    ret

whereToAbstract1
  :: Range                            -- ^ The range of the @where@-block.
  -> Maybe (C.Name, Access)           -- ^ The name of the @where@ module (if any).
  -> List1 C.Declaration              -- ^ The contents of the @where@ module.
  -> ScopeM a                         -- ^ The scope-checking task to be run in the context of the @where@ module.
  -> ScopeM (a, A.WhereDeclarations)  -- ^ Additionally return the scope-checked contents of the @where@ module.
whereToAbstract1 r whname whds inner = do
  -- ASR (16 November 2015) Issue 1137: We ban termination
  -- pragmas inside `where` clause.
  checkNoTerminationPragma InWhereBlock whds

  -- Create a fresh concrete name if there isn't (a proper) one.
  (m, acc) <- do
    case whname of
      Just (m, acc) | not (isNoName m) -> return (m, acc)
      _ -> fresh <&> \ x -> (C.NoName (getRange whname) x, PrivateAccess Inserted)
           -- unnamed where's are private
  old <- getCurrentModule
  am  <- toAbstract (NewModuleName m)
  (scope, d) <- scopeCheckModule r (C.QName m) am [] $ toAbstract $ Declarations $ List1.toList whds
  setScope scope
  x <- inner
  setCurrentModule old
  bindModule acc m am
  -- Issue 848: if the module was anonymous (module _ where) open it public
  let anonymousSomeWhere = maybe False (isNoName . fst) whname
  when anonymousSomeWhere $
   void $ -- We can ignore the returned default A.ImportDirective.
    openModule TopOpenModule (Just am) (C.QName m) $
      defaultImportDir { publicOpen = Just noRange }
  return (x, A.WhereDecls (am <$ whname) $ singleton d)

data TerminationOrPositivity = Termination | Positivity
  deriving (Show)

data WhereOrRecord = InWhereBlock | InRecordDef

checkNoTerminationPragma :: Foldable f => WhereOrRecord -> f C.Declaration -> ScopeM ()
checkNoTerminationPragma b ds =
  mapM_ (\ (p, r) -> warning $ GenericUseless r $ P.vcat [ P.text $ show p ++ " pragmas are ignored in " ++ what b
                                                         , P.text $ "(see " ++ issue b ++ ")" ])
        (foldMap terminationPragmas ds)
  where
    what InWhereBlock = "where clauses"
    what InRecordDef  = "record definitions"
    github n = "https://github.com/agda/agda/issues/" ++ show n
    issue InWhereBlock = github 3355
    issue InRecordDef  = github 3008

terminationPragmas :: C.Declaration -> [(TerminationOrPositivity, Range)]
terminationPragmas (C.Private  _ _      ds) = concatMap terminationPragmas ds
terminationPragmas (C.Abstract _        ds) = concatMap terminationPragmas ds
terminationPragmas (C.InstanceB _       ds) = concatMap terminationPragmas ds
terminationPragmas (C.Mutual _          ds) = concatMap terminationPragmas ds
terminationPragmas (C.Module _ _ _      ds) = concatMap terminationPragmas ds
terminationPragmas (C.Macro _           ds) = concatMap terminationPragmas ds
terminationPragmas (C.Record _ _ _ _ _  ds) = concatMap terminationPragmas ds
terminationPragmas (C.RecordDef _ _ _ _ ds) = concatMap terminationPragmas ds
terminationPragmas (C.Pragma (TerminationCheckPragma r _)) = [(Termination, r)]
terminationPragmas (C.Pragma (NoPositivityCheckPragma r))  = [(Positivity, r)]
terminationPragmas _                                       = []

data RightHandSide = RightHandSide
  { _rhsRewriteEqn :: [RewriteEqn' () A.BindName A.Pattern A.Expr]
    -- ^ @rewrite e | with p <- e in eq@ (many)
  , _rhsWithExpr   :: [C.WithExpr]
    -- ^ @with e@ (many)
  , _rhsSubclauses :: (LocalVars, [C.Clause])
    -- ^ the subclauses spawned by a with (monadic because we need to reset the local vars before checking these clauses)
  , _rhs           :: C.RHS
  , _rhsWhere      :: WhereClause
      -- ^ @where@ module.
  }

data AbstractRHS
  = AbsurdRHS'
  | WithRHS' [A.WithExpr] [ScopeM C.Clause]
    -- ^ The with clauses haven't been translated yet
  | RHS' A.Expr C.Expr
  | RewriteRHS' [RewriteEqn' () A.BindName A.Pattern A.Expr] AbstractRHS A.WhereDeclarations

qualifyName_ :: A.Name -> ScopeM A.QName
qualifyName_ x = do
  m <- getCurrentModule
  return $ A.qualify m x

withFunctionName :: String -> ScopeM A.QName
withFunctionName s = do
  NameId i _ <- fresh
  qualifyName_ =<< freshName_ (s ++ show i)

instance ToAbstract (RewriteEqn' () A.BindName A.Pattern A.Expr) where
  type AbsOfCon (RewriteEqn' () A.BindName A.Pattern A.Expr) = A.RewriteEqn
  toAbstract = \case
    Rewrite es -> fmap Rewrite $ forM es $ \ (_, e) -> do
      qn <- withFunctionName "-rewrite"
      pure (qn, e)
    Invert _ pes -> do
      qn <- withFunctionName "-invert"
      pure $ Invert qn pes

instance ToAbstract C.RewriteEqn where
  type AbsOfCon C.RewriteEqn = RewriteEqn' () A.BindName A.Pattern A.Expr
  toAbstract = \case
    Rewrite es   -> Rewrite <$> mapM toAbstract es
    Invert _ npes -> Invert () <$> do
      -- Given a list of irrefutable with expressions of the form @p <- e in q@
      let (nps, es) = List1.unzip
                    $ fmap (\ (Named nm (p, e)) -> ((nm, p), e)) npes
      -- we first check the expressions @e@: the patterns may shadow some of the
      -- variables mentioned in them!
      es <- toAbstract es
      -- we then parse the pairs of patterns @p@ and names @q@ for the equality
      -- constraints of the form @p ≡ e@.
      nps <- forM nps $ \ (n, p) -> do
        -- first the pattern
        p <- parsePattern p
        p <- toAbstract p
        checkPatternLinearity p (typeError . RepeatedVariablesInPattern)
        bindVarsToBind
        p <- toAbstract p
        -- and then the name
        n <- toAbstract $ fmap (NewName WithBound . C.mkBoundName_) n
        pure (n, p)
      -- we finally reassemble the telescope
      pure $ List1.zipWith (\ (n,p) e -> Named n (p, e)) nps es

instance ToAbstract AbstractRHS where
  type AbsOfCon AbstractRHS = A.RHS

  toAbstract AbsurdRHS'            = return A.AbsurdRHS
  toAbstract (RHS' e c)            = return $ A.RHS e $ Just c
  toAbstract (RewriteRHS' eqs rhs wh) = do
    eqs <- toAbstract eqs
    rhs <- toAbstract rhs
    return $ RewriteRHS eqs [] rhs wh
  toAbstract (WithRHS' es cs) = do
    aux <- withFunctionName "with-"
    A.WithRHS aux es <$> do toAbstract =<< sequence cs

instance ToAbstract RightHandSide where
  type AbsOfCon RightHandSide = AbstractRHS
  toAbstract (RightHandSide eqs@(_:_) es cs rhs wh)               = do
    (rhs, ds) <- whereToAbstract (getRange wh) wh $
                   toAbstract (RightHandSide [] es cs rhs NoWhere)
    return $ RewriteRHS' eqs rhs ds
  toAbstract (RightHandSide [] []    (_  , _:_) _          _)  = __IMPOSSIBLE__
  toAbstract (RightHandSide [] (_:_) _         (C.RHS _)   _)  = typeError $ BothWithAndRHS
  toAbstract (RightHandSide [] []    (_  , []) rhs         NoWhere) = toAbstract rhs
  toAbstract (RightHandSide [] nes   (lv , cs) C.AbsurdRHS NoWhere) = do
    let (ns , es) = unzipWith (\ (Named nm e) -> (NewName WithBound . C.mkBoundName_ <$> nm, e)) nes
    es <- toAbstractCtx TopCtx es
    lvars0 <- getLocalVars
    ns <- toAbstract ns
    lvars1 <- getLocalVars
    let lv' = dropEnd (length lvars0) lvars1 ++ lv
    let cs' = for cs $ \ c -> setLocalVars lv' $> c
    let nes = zipWith Named ns es
    return $ WithRHS' nes cs'
  -- TODO: some of these might be possible
  toAbstract (RightHandSide [] (_ : _) _ C.AbsurdRHS  AnyWhere{}) = __IMPOSSIBLE__
  toAbstract (RightHandSide [] (_ : _) _ C.AbsurdRHS SomeWhere{}) = __IMPOSSIBLE__
  toAbstract (RightHandSide [] []     (_, []) C.AbsurdRHS  AnyWhere{}) = __IMPOSSIBLE__
  toAbstract (RightHandSide [] []     (_, []) C.AbsurdRHS SomeWhere{}) = __IMPOSSIBLE__
  toAbstract (RightHandSide [] []     (_, []) C.RHS{}      AnyWhere{}) = __IMPOSSIBLE__
  toAbstract (RightHandSide [] []     (_, []) C.RHS{}     SomeWhere{}) = __IMPOSSIBLE__

instance ToAbstract C.RHS where
    type AbsOfCon C.RHS = AbstractRHS

    toAbstract C.AbsurdRHS = return $ AbsurdRHS'
    toAbstract (C.RHS e)   = RHS' <$> toAbstract e <*> pure e

data LeftHandSide = LeftHandSide C.QName C.Pattern

instance ToAbstract LeftHandSide where
    type AbsOfCon LeftHandSide = A.LHS

    toAbstract (LeftHandSide top lhs) =
      traceCall (ScopeCheckLHS top lhs) $ do
        reportSLn "scope.lhs" 5 $ "original lhs: " ++ prettyShow lhs
        reportSLn "scope.lhs" 60 $ "patternQNames: " ++ prettyShow (patternQNames lhs)
        reportSLn "scope.lhs" 60 $ "original lhs (raw): " ++ show lhs
        lhscore <- parseLHS top lhs
        let ell = hasExpandedEllipsis lhscore
        reportSLn "scope.lhs" 5 $ "parsed lhs: " ++ prettyShow lhscore
        reportSLn "scope.lhs" 60 $ "parsed lhs (raw): " ++ show lhscore
        printLocals 10 "before lhs:"
        -- error if copattern parsed but --no-copatterns option
        unlessM (optCopatterns <$> pragmaOptions) $
          when (hasCopatterns lhscore) $
            typeError $ NeedOptionCopatterns
        -- scope check patterns except for dot patterns
        lhscore <- toAbstract lhscore
        bindVarsToBind
        -- reportSLn "scope.lhs" 5 $ "parsed lhs patterns: " ++ prettyShow lhscore  -- TODO: Pretty A.LHSCore'
        reportSLn "scope.lhs" 60 $ "parsed lhs patterns: " ++ show lhscore
        printLocals 10 "checked pattern:"
        -- scope check dot patterns
        lhscore <- toAbstract lhscore
        -- reportSLn "scope.lhs" 5 $ "parsed lhs dot patterns: " ++ prettyShow lhscore  -- TODO: Pretty A.LHSCore'
        reportSLn "scope.lhs" 60 $ "parsed lhs dot patterns: " ++ show lhscore
        printLocals 10 "checked dots:"
        return $ A.LHS (LHSInfo (getRange lhs) ell) lhscore

hasExpandedEllipsis :: C.LHSCore -> ExpandedEllipsis
hasExpandedEllipsis core = case core of
  C.LHSHead{}       -> NoEllipsis
  C.LHSProj{}       -> hasExpandedEllipsis $ namedArg $ C.lhsFocus core -- can this ever be ExpandedEllipsis?
  C.LHSWith{}       -> hasExpandedEllipsis $ C.lhsHead core
  C.LHSEllipsis r p -> case p of
    C.LHSWith _ wps _ -> ExpandedEllipsis r (length wps)
    C.LHSHead{}       -> ExpandedEllipsis r 0
    C.LHSProj{}       -> ExpandedEllipsis r 0
    C.LHSEllipsis{}   -> __IMPOSSIBLE__

-- | Merges adjacent EqualP patterns into one:
-- type checking expects only one pattern for each domain in the telescope.
mergeEqualPs :: [NamedArg (Pattern' e)] -> ScopeM [NamedArg (Pattern' e)]
mergeEqualPs = go (empty, [])
  where
    go acc (p@(Arg i (Named mn (A.EqualP r es))) : ps) = setCurrentRange p $ do
      -- Face constraint patterns must be defaultNamedArg; check this:
      unless (getModality i == defaultModality) __IMPOSSIBLE__
      when (hidden     i) $ warn i $ "Face constraint patterns cannot be hidden arguments"
      when (isInstance i) $ warn i $ "Face constraint patterns cannot be instance arguments"
      whenJust mn $ \ x -> setCurrentRange x $ warn x $ P.hcat
          [ "Ignoring name `", P.pretty x, "` given to face constraint pattern" ]
      go (acc `mappend` (r, es)) ps
    go (r, es@(_:_)) ps = (defaultNamedArg (A.EqualP r es) :) <$> mergeEqualPs ps
    go (_, []) []       = return []
    go (_, []) (p : ps) = (p :) <$> mergeEqualPs ps

    warn r d = warning $ GenericUseless (getRange r) d

-- does not check pattern linearity
instance ToAbstract C.LHSCore where
    type AbsOfCon C.LHSCore = (A.LHSCore' C.Expr)

    toAbstract (C.LHSHead x ps) = do
        x <- withLocalVars $ do
          setLocalVars []
          toAbstract (OldName x)
        A.LHSHead x <$> do mergeEqualPs =<< toAbstract ps
    toAbstract (C.LHSProj d ps1 l ps2) = do
        unless (null ps1) $ typeError $ GenericDocError $
          "Ill-formed projection pattern" P.<+> P.pretty (foldl C.AppP (C.IdentP d) ps1)
        qx <- resolveName d
        ds <- case qx of
                FieldName ds -> return $ fmap anameName ds
                UnknownName -> notInScopeError d
                _           -> genericError $
                  "head of copattern needs to be a field identifier, but "
                  ++ prettyShow d ++ " isn't one"
        A.LHSProj (AmbQ ds) <$> toAbstract l <*> (mergeEqualPs =<< toAbstract ps2)
    toAbstract (C.LHSWith core wps ps) = do
      liftA2 A.lhsCoreApp
        (liftA2 A.lhsCoreWith
          (toAbstract core)
          (map defaultArg <$> toAbstract wps))
        (toAbstract ps)
    -- In case of a part of the LHS which was expanded from an ellipsis,
    -- we flush the @scopeVarsToBind@ in order to allow variables bound
    -- in the ellipsis to be shadowed.
    toAbstract (C.LHSEllipsis _ p) = do
      ap <- toAbstract p
      bindVarsToBind
      return ap

instance ToAbstract c => ToAbstract (WithHiding c) where
  type AbsOfCon (WithHiding c) = WithHiding (AbsOfCon c)
  toAbstract (WithHiding h a) = WithHiding h <$> toAbstractHiding h a

instance ToAbstract c => ToAbstract (Arg c) where
    type AbsOfCon (Arg c) = Arg (AbsOfCon c)
    toAbstract (Arg info e) =
        Arg info <$> toAbstractHiding info e

instance ToAbstract c => ToAbstract (Named name c) where
    type AbsOfCon (Named name c) = Named name (AbsOfCon c)
    toAbstract (Named n e) = Named n <$> toAbstract e

{- DOES NOT WORK ANYMORE with pattern synonyms
instance ToAbstract c a => ToAbstract (A.LHSCore' c) (A.LHSCore' a) where
    toAbstract = mapM toAbstract
-}

instance ToAbstract (A.LHSCore' C.Expr) where
    type AbsOfCon (A.LHSCore' C.Expr) = A.LHSCore' A.Expr
    toAbstract (A.LHSHead f ps)         = A.LHSHead f <$> mapM toAbstract ps
    toAbstract (A.LHSProj d lhscore ps) = A.LHSProj d <$> mapM toAbstract lhscore <*> mapM toAbstract ps
    toAbstract (A.LHSWith core wps ps)  = liftA3 A.LHSWith (toAbstract core) (toAbstract wps) (toAbstract ps)

-- Patterns are done in two phases. First everything but the dot patterns, and
-- then the dot patterns. This is because dot patterns can refer to variables
-- bound anywhere in the pattern.

instance ToAbstract (A.Pattern' C.Expr) where
  type AbsOfCon (A.Pattern' C.Expr) = A.Pattern' A.Expr
  toAbstract = traverse $ insideDotPattern . toAbstractCtx DotPatternCtx  -- Issue #3033

resolvePatternIdentifier ::
  Range -> C.QName -> Maybe (Set A.Name) -> ScopeM (A.Pattern' C.Expr)
resolvePatternIdentifier r x ns = do
  reportSLn "scope.pat" 60 $ "resolvePatternIdentifier " ++ prettyShow x ++ " at source position " ++ prettyShow r
  px <- toAbstract (PatName x ns)
  case px of
    VarPatName y         -> do
      reportSLn "scope.pat" 60 $ "  resolved to VarPatName " ++ prettyShow y ++ " with range " ++ prettyShow (getRange y)
      return $ VarP $ A.mkBindName y
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
        ConstructorName _ ds -> do
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
      A.AnnP{}    -> failure
  where
    failure = typeError $ InvalidPattern p0

instance ToAbstract C.Pattern where
    type AbsOfCon C.Pattern = A.Pattern' C.Expr

    toAbstract (C.IdentP x) =
      resolvePatternIdentifier (getRange x) x Nothing

    toAbstract (AppP (QuoteP _) p)
      | IdentP x <- namedArg p,
        visible p = do
      e <- toAbstract (OldQName x Nothing)
      A.LitP (PatRange $ getRange x) . LitQName <$> quotedName e

    toAbstract (QuoteP r) =
      genericError "quote must be applied to an identifier"

    toAbstract p0@(AppP p q) = do
        reportSLn "scope.pat" 50 $ "distributeDots before = " ++ show p
        p <- distributeDots p
        reportSLn "scope.pat" 50 $ "distributeDots after  = " ++ show p
        (p', q') <- toAbstract (p, q)
        applyAPattern p0 p' $ singleton q'

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

    toAbstract (EllipsisP _ mp) = maybe __IMPOSSIBLE__ toAbstract mp

    -- Removed when parsing
    toAbstract (HiddenP _ _)   = __IMPOSSIBLE__
    toAbstract (InstanceP _ _) = __IMPOSSIBLE__
    toAbstract (RawAppP _ _)   = __IMPOSSIBLE__

    toAbstract p@(C.WildP r)    = return $ A.WildP (PatRange r)
    -- Andreas, 2015-05-28 futile attempt to fix issue 819: repeated variable on lhs "_"
    -- toAbstract p@(C.WildP r)    = A.VarP <$> freshName r "_"
    toAbstract (C.ParenP _ p)   = toAbstract p
    toAbstract (C.LitP r l)     = setCurrentRange r $ A.LitP (PatRange r) l <$ checkLiteral l

    toAbstract p0@(C.AsP r x p) = do
        -- Andreas, 2018-06-30, issue #3147: as-variables can be non-linear a priori!
        -- x <- toAbstract (NewName PatternBound x)
        -- Andreas, 2020-05-01, issue #4631: as-variables should not shadow constructors.
        -- x <- bindPatternVariable x
      toAbstract (PatName (C.QName x) Nothing) >>= \case
        VarPatName x        -> A.AsP (PatRange r) (A.mkBindName x) <$> toAbstract p
        ConPatName{}        -> ignoreAsPat False
        PatternSynPatName{} -> ignoreAsPat True
      where
      -- An @-bound name which shadows a constructor is illegal and becomes dead code.
      ignoreAsPat b = do
        setCurrentRange x $ warning $ AsPatternShadowsConstructorOrPatternSynonym b
        toAbstract p

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
toAbstractOpApp :: C.QName -> Set A.Name -> OpAppArgs -> ScopeM A.Expr
toAbstractOpApp op ns es = do
    -- Replace placeholders with bound variables.
    (binders, es) <- replacePlaceholders es
    -- Get the notation for the operator.
    nota <- getNotation op ns
    let parts = notation nota
    -- We can throw away the @VarPart@s, since binders
    -- have been preprocessed into @OpApp C.Expr@.
    let nonBindingParts = filter (not . isBinder) parts
    -- We should be left with as many holes as we have been given args @es@.
    -- If not, crash.
    unless (length (filter isAHole nonBindingParts) == length es) __IMPOSSIBLE__
    -- Translate operator and its arguments (each in the right context).
    op <- toAbstract (OldQName op (Just ns))
    es <- left (notaFixity nota) nonBindingParts es
    -- Prepend the generated section binders (if any).
    let body = List.foldl' app op es
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
      OpAppArgs' e ->
      ScopeM ([A.LamBinding], [NamedArg (Either A.Expr (OpApp e))])
    replacePlaceholders []       = return ([], [])
    replacePlaceholders (a : as) = case namedArg a of
      NoPlaceholder _ x -> mapSnd (set (Right x) a :) <$>
                             replacePlaceholders as
      Placeholder _     -> do
        x <- freshName noRange "section"
        let i = setOrigin Inserted $ argInfo a
        (ls, ns) <- replacePlaceholders as
        return ( A.mkDomainFree (unnamedArg i $ A.mkBinder_ x) : ls
               , set (Left (Var x)) a : ns
               )
      where
      set :: a -> NamedArg b -> NamedArg a
      set x arg = fmap (fmap (const x)) arg


{--------------------------------------------------------------------------
    Things we parse but are not part of the Agda file syntax
 --------------------------------------------------------------------------}

-- | Content of interaction hole.

instance ToAbstract C.HoleContent where
  type AbsOfCon C.HoleContent = A.HoleContent
  toAbstract = \case
    HoleContentExpr e     -> HoleContentExpr <$> toAbstract e
    HoleContentRewrite es -> HoleContentRewrite <$> toAbstract es
