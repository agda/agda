
module Agda.Syntax.Abstract.Views where

import Prelude hiding (null)

import Control.Applicative ( Const(Const), getConst )
import Control.Arrow (first)
import Control.Monad.Identity

import Data.Foldable (foldMap)
import qualified Data.DList as DL
import Data.Semigroup ((<>))
import Data.Void

import Agda.Syntax.Common
import Agda.Syntax.Abstract as A
import Agda.Syntax.Concrete (FieldAssignment', exprFieldA)
import Agda.Syntax.Info
import Agda.Syntax.Scope.Base (KindOfName(..), conKindOfName, WithKind(..))

import Agda.Utils.Either
import Agda.Utils.List1 (List1)
import Agda.Utils.Null
import Agda.Utils.Singleton

import Agda.Utils.Impossible


data AppView' arg = Application Expr [NamedArg arg]
  deriving (Functor)

type AppView = AppView' Expr

-- | Gather applications to expose head and spine.
--
--   Note: everything is an application, possibly of itself to 0 arguments
appView :: Expr -> AppView
appView = fmap snd . appView'

appView' :: Expr -> AppView' (AppInfo, Expr)
appView' e = f (DL.toList es)
  where
  (f, es) = appView'' e

  appView'' e = case e of
    App i e1 e2
      | Dot _ e2' <- unScope $ namedArg e2
      , Just f <- maybeProjTurnPostfix e2'
      , getHiding e2 == NotHidden -- Jesper, 2018-12-13: postfix projections shouldn't be hidden
      -> (Application f, singleton (defaultNamedArg (i, e1)))
    App i e1 arg | (f, es) <- appView'' e1 ->
      (f, es `DL.snoc` (fmap . fmap) (i,) arg)
    ScopedExpr _ e -> appView'' e
    _              -> (Application e, mempty)

maybeProjTurnPostfix :: Expr -> Maybe Expr
maybeProjTurnPostfix e =
  case e of
    ScopedExpr i e' -> ScopedExpr i <$> maybeProjTurnPostfix e'
    Proj _ x        -> return $ Proj ProjPostfix x
    _               -> Nothing

unAppView :: AppView -> Expr
unAppView (Application h es) =
  foldl (App defaultAppInfo_) h es

-- | Collects plain lambdas.
data LamView = LamView [LamBinding] Expr

lamView :: Expr -> LamView
lamView (Lam i b e) = cons b $ lamView e
  where cons b (LamView bs e) = LamView (b : bs) e
lamView (ScopedExpr _ e) = lamView e
lamView e = LamView [] e

-- | Collect @A.Pi@s.
data PiView = PiView [(ExprInfo, Telescope1)] Type

piView :: Expr -> PiView
piView = \case
   Pi i tel b -> cons $ piView b
     where cons (PiView tels t) = PiView ((i,tel) : tels) t
   e -> PiView [] e

unPiView :: PiView -> Expr
unPiView (PiView tels t) = foldr (uncurry Pi) t tels

-- | Gather top-level 'AsP'atterns and 'AnnP'atterns to expose underlying pattern.
asView :: A.Pattern -> ([Name], [A.Expr], A.Pattern)
asView (A.AsP _ x p)  = (\(asb, ann, p) -> (unBind x : asb, ann, p)) $ asView p
asView (A.AnnP _ a p) = (\(asb, ann, p) -> (asb, a : ann, p))        $ asView p
asView p              = ([], [], p)

-- | Remove top 'ScopedExpr' wrappers.
unScope :: Expr -> Expr
unScope (ScopedExpr scope e) = unScope e
unScope (QuestionMark i ii)  = QuestionMark (i {metaScope = empty}) ii
unScope (Underscore i)       = Underscore (i {metaScope = empty})
unScope e                    = e

-- | Remove 'ScopedExpr' wrappers everywhere.
--
--   NB: Unless the implementation of 'ExprLike' for clauses
--   has been finished, this does not work for clauses yet.
deepUnscope :: ExprLike a => a -> a
deepUnscope = mapExpr unScope

deepUnscopeDecls :: [A.Declaration] -> [A.Declaration]
deepUnscopeDecls = concatMap deepUnscopeDecl

deepUnscopeDecl :: A.Declaration -> [A.Declaration]
deepUnscopeDecl = \case
  A.ScopedDecl _ ds           -> deepUnscopeDecls ds
  A.Mutual i ds               -> [A.Mutual i (deepUnscopeDecls ds)]
  A.Section i e m tel ds      -> [A.Section i e m (deepUnscope tel)
                                   (deepUnscopeDecls ds)]
  A.RecDef i x uc dir bs e ds -> [ A.RecDef i x uc dir (deepUnscope bs)
                                     (deepUnscope e)
                                     (deepUnscopeDecls ds) ]
  d                           -> [deepUnscope d]

-- * Traversal
---------------------------------------------------------------------------

-- Type aliases to abbreviate the quantified foralls which we use to avoid
-- giving in to NoMonoLocalBinds.
type RecurseExprFn m a = Applicative m => (Expr -> m Expr -> m Expr) -> a -> m a
type RecurseExprRecFn m = forall a. ExprLike a => a -> m a

type FoldExprFn m a = Monoid m => (Expr -> m) -> a -> m
type FoldExprRecFn m = forall a. ExprLike a => a -> m

type TraverseExprFn m a = (Applicative m, Monad m) => (Expr -> m Expr) -> a -> m a
type TraverseExprRecFn m = forall a. ExprLike a => a -> m a

-- | Apply an expression rewriting to every subexpression, inside-out.
--   See "Agda.Syntax.Internal.Generic".
class ExprLike a where
  -- | The first expression is pre-traversal, the second one post-traversal.
  recurseExpr :: RecurseExprFn m a
  default recurseExpr :: (Traversable f, ExprLike a', a ~ f a', Applicative m)
                      => (Expr -> m Expr -> m Expr) -> a -> m a
  recurseExpr = traverse . recurseExpr

  foldExpr :: FoldExprFn m a
  foldExpr f = getConst . recurseExpr (\ pre post -> Const (f pre) <* post)

  traverseExpr :: TraverseExprFn m a
  traverseExpr f = recurseExpr (\ pre post -> f =<< post)

  mapExpr :: (Expr -> Expr) -> (a -> a)
  mapExpr f = runIdentity . traverseExpr (Identity . f)

instance ExprLike Expr where
  recurseExpr :: forall m. RecurseExprFn m Expr
  recurseExpr f e0 = f e0 $ do
    let
      recurse :: RecurseExprRecFn m
      recurse e = recurseExpr f e
    case e0 of
      Var{}                      -> pure e0
      Def'{}                     -> pure e0
      Proj{}                     -> pure e0
      Con{}                      -> pure e0
      Lit{}                      -> pure e0
      QuestionMark{}             -> pure e0
      Underscore{}               -> pure e0
      Dot ei e                   -> Dot ei <$> recurse e
      App ei e arg               -> App ei <$> recurse e <*> recurse arg
      WithApp ei e es            -> WithApp ei <$> recurse e <*> recurse es
      Lam ei b e                 -> Lam ei <$> recurse b <*> recurse e
      AbsurdLam{}                -> pure e0
      ExtendedLam ei di er x cls -> ExtendedLam ei di er x <$> recurse cls
      Pi ei tel e                -> Pi ei <$> recurse tel <*> recurse e
      Generalized  s e           -> Generalized s <$> recurse e
      Fun ei arg e               -> Fun ei <$> recurse arg <*> recurse e
      Let ei bs e                -> Let ei <$> recurse bs <*> recurse e
      Rec ei bs                  -> Rec ei <$> recurse bs
      RecUpdate ei e bs          -> RecUpdate ei <$> recurse e <*> recurse bs
      ScopedExpr sc e            -> ScopedExpr sc <$> recurse e
      Quote{}                    -> pure e0
      QuoteTerm{}                -> pure e0
      Unquote{}                  -> pure e0
      DontCare e                 -> DontCare <$> recurse e
      PatternSyn{}               -> pure e0
      Macro{}                    -> pure e0

  foldExpr :: forall m. FoldExprFn m Expr
  foldExpr f e =
    case e of
      Var{}                  -> m
      Def'{}                 -> m
      Proj{}                 -> m
      Con{}                  -> m
      PatternSyn{}           -> m
      Macro{}                -> m
      Lit{}                  -> m
      QuestionMark{}         -> m
      Underscore{}           -> m
      Dot _ e                -> m `mappend` fold e
      App _ e e'             -> m `mappend` fold e `mappend` fold e'
      WithApp _ e es         -> m `mappend` fold e `mappend` fold es
      Lam _ b e              -> m `mappend` fold b `mappend` fold e
      AbsurdLam{}            -> m
      ExtendedLam _ _ _ _ cs -> m `mappend` fold cs
      Pi _ tel e             -> m `mappend` fold tel `mappend` fold e
      Generalized _ e        -> m `mappend` fold e
      Fun _ e e'             -> m `mappend` fold e `mappend` fold e'
      Let _ bs e             -> m `mappend` fold bs `mappend` fold e
      Rec _ as               -> m `mappend` fold as
      RecUpdate _ e as       -> m `mappend` fold e `mappend` fold as
      ScopedExpr _ e         -> m `mappend` fold e
      Quote{}                -> m
      QuoteTerm{}            -> m
      Unquote{}              -> m
      DontCare e             -> m `mappend` fold e
   where
     m = f e
     fold :: FoldExprRecFn m
     fold = foldExpr f

  traverseExpr :: forall m. TraverseExprFn m Expr
  traverseExpr f e = do
    let
      trav :: TraverseExprRecFn m
      trav e = traverseExpr f e
    case e of
      Var{}                      -> f e
      Def'{}                     -> f e
      Proj{}                     -> f e
      Con{}                      -> f e
      Lit{}                      -> f e
      QuestionMark{}             -> f e
      Underscore{}               -> f e
      Dot ei e                   -> f =<< Dot ei <$> trav e
      App ei e arg               -> f =<< App ei <$> trav e <*> trav arg
      WithApp ei e es            -> f =<< WithApp ei <$> trav e <*> trav es
      Lam ei b e                 -> f =<< Lam ei <$> trav b <*> trav e
      AbsurdLam{}                -> f e
      ExtendedLam ei di re x cls -> f =<< ExtendedLam ei di re x <$> trav cls
      Pi ei tel e                -> f =<< Pi ei <$> trav tel <*> trav e
      Generalized s e            -> f =<< Generalized s <$> trav e
      Fun ei arg e               -> f =<< Fun ei <$> trav arg <*> trav e
      Let ei bs e                -> f =<< Let ei <$> trav bs <*> trav e
      Rec ei bs                  -> f =<< Rec ei <$> trav bs
      RecUpdate ei e bs          -> f =<< RecUpdate ei <$> trav e <*> trav bs
      ScopedExpr sc e            -> f =<< ScopedExpr sc <$> trav e
      Quote{}                    -> f e
      QuoteTerm{}                -> f e
      Unquote{}                  -> f e
      DontCare e                 -> f =<< DontCare <$> trav e
      PatternSyn{}               -> f e
      Macro{}                    -> f e

instance ExprLike a => ExprLike (Arg a)
instance ExprLike a => ExprLike (Maybe a)
instance ExprLike a => ExprLike (Named x a)
instance ExprLike a => ExprLike [a]
instance ExprLike a => ExprLike (List1 a)

instance (ExprLike a, ExprLike b) => ExprLike (a, b) where
  recurseExpr f (x, y) = (,) <$> recurseExpr f x <*> recurseExpr f y

instance ExprLike Void where
  recurseExpr f = absurd

instance ExprLike a => ExprLike (FieldAssignment' a) where
  recurseExpr = exprFieldA . recurseExpr

instance (ExprLike a, ExprLike b) => ExprLike (Either a b) where
  recurseExpr f = traverseEither (recurseExpr f)
                                 (recurseExpr f)

instance ExprLike BindName where
  recurseExpr f = pure

instance ExprLike ModuleName where
  recurseExpr f = pure

instance ExprLike QName where
  recurseExpr _ = pure

instance ExprLike LamBinding where
  recurseExpr f e =
    case e of
      DomainFree t x -> DomainFree <$> recurseExpr f t <*> pure x
      DomainFull bs  -> DomainFull <$> recurseExpr f bs
  foldExpr f e =
    case e of
      DomainFree t _ -> foldExpr f t
      DomainFull bs -> foldExpr f bs
  traverseExpr f e =
    case e of
      DomainFree t x -> DomainFree <$> traverseExpr f t <*> pure x
      DomainFull bs  -> DomainFull <$> traverseExpr f bs

instance ExprLike GeneralizeTelescope where
  recurseExpr  f (GeneralizeTel s tel) = GeneralizeTel s <$> recurseExpr f tel
  foldExpr     f (GeneralizeTel s tel) = foldExpr f tel
  traverseExpr f (GeneralizeTel s tel) = GeneralizeTel s <$> traverseExpr f tel

instance ExprLike DataDefParams where
  recurseExpr  f (DataDefParams s tel) = DataDefParams s <$> recurseExpr f tel
  foldExpr     f (DataDefParams s tel) = foldExpr f tel
  traverseExpr f (DataDefParams s tel) = DataDefParams s <$> traverseExpr f tel

instance ExprLike TypedBindingInfo where
  recurseExpr f (TypedBindingInfo s t)  = TypedBindingInfo <$> recurseExpr f s <*> pure t
  foldExpr f (TypedBindingInfo s t)     = foldExpr f s
  traverseExpr f (TypedBindingInfo s t) = TypedBindingInfo <$> traverseExpr f s <*> pure t

instance ExprLike TypedBinding where
  recurseExpr f e =
    case e of
      TBind r t xs e -> TBind r <$> recurseExpr f t <*> pure xs <*> recurseExpr f e
      TLet r ds      -> TLet r <$> recurseExpr f ds
  foldExpr f e =
    case e of
      TBind _ t _ e -> foldExpr f t `mappend` foldExpr f e
      TLet _ ds     -> foldExpr f ds
  traverseExpr f e =
    case e of
      TBind r t xs e -> TBind r <$> traverseExpr f t <*> pure xs <*> traverseExpr f e
      TLet r ds      -> TLet r <$> traverseExpr f ds

instance ExprLike LetBinding where
  recurseExpr :: forall m. RecurseExprFn m LetBinding
  recurseExpr f e = do
    let
      recurse :: RecurseExprRecFn m
      recurse e = recurseExpr f e
    case e of
      LetBind li ai x e e'  -> LetBind li ai x <$> recurse e <*> recurse e'
      LetPatBind li p e     -> LetPatBind li <$> recurse p <*> recurse e
      LetApply{}            -> pure e
      LetOpen{}             -> pure e
      LetDeclaredVariable _ -> pure e

  foldExpr :: forall m. FoldExprFn m LetBinding
  foldExpr f e =
    case e of
      LetBind _ _ _ e e'    -> fold e `mappend` fold e'
      LetPatBind _ p e      -> fold p `mappend` fold e
      LetApply{}            -> mempty
      LetOpen{}             -> mempty
      LetDeclaredVariable _ -> mempty
    where
      fold :: FoldExprRecFn m
      fold e = foldExpr f e

  traverseExpr :: forall m. TraverseExprFn m LetBinding
  traverseExpr f e = do
    let
      trav :: TraverseExprRecFn m
      trav e = traverseExpr f e
    case e of
      LetBind li ai x e e'  -> LetBind li ai x <$> trav e <*> trav e'
      LetPatBind li p e     -> LetPatBind li <$> trav p <*> trav e
      LetApply{}            -> pure e
      LetOpen{}             -> pure e
      LetDeclaredVariable _ -> pure e

instance ExprLike a => ExprLike (Pattern' a) where

instance ExprLike a => ExprLike (Clause' a) where
  recurseExpr :: forall m. RecurseExprFn m (Clause' a)
  recurseExpr f (Clause lhs spats rhs ds ca) = Clause <$> rec lhs <*> pure spats <*> rec rhs <*> rec ds <*> pure ca
    where
      rec :: RecurseExprRecFn m
      rec = recurseExpr f

instance ExprLike RHS where
  recurseExpr :: forall m. RecurseExprFn m RHS
  recurseExpr f rhs =
    case rhs of
      RHS e c                 -> RHS <$> rec e <*> pure c
      AbsurdRHS{}             -> pure rhs
      WithRHS x es cs         -> WithRHS x <$> rec es <*> rec cs
      RewriteRHS xes spats rhs ds -> RewriteRHS <$> rec xes <*> pure spats <*> rec rhs <*> rec ds
    where
      rec :: RecurseExprRecFn m
      rec e = recurseExpr f e

instance (ExprLike qn, ExprLike nm, ExprLike p, ExprLike e) => ExprLike (RewriteEqn' qn nm p e) where
  recurseExpr f = \case
    Rewrite es    -> Rewrite <$> recurseExpr f es
    Invert qn pes -> Invert <$> recurseExpr f qn <*> recurseExpr f pes

instance ExprLike WhereDeclarations where
  recurseExpr f (WhereDecls a b c) = WhereDecls a b <$> recurseExpr f c

instance ExprLike ModuleApplication where
  recurseExpr :: forall m. RecurseExprFn m ModuleApplication
  recurseExpr f a =
    case a of
      SectionApp tel m es -> SectionApp <$> rec tel <*> rec m <*> rec es
      RecordModuleInstance{} -> pure a
    where
      rec :: RecurseExprRecFn m
      rec e = recurseExpr f e

instance ExprLike Pragma where
  recurseExpr :: forall m. RecurseExprFn m Pragma
  recurseExpr f p =
    case p of
      BuiltinPragma s x           -> pure p
      OptionsPragma{}             -> pure p
      BuiltinNoDefPragma{}        -> pure p
      RewritePragma{}             -> pure p
      CompilePragma{}             -> pure p
      StaticPragma{}              -> pure p
      InjectivePragma{}           -> pure p
      InlinePragma{}              -> pure p
      EtaPragma{}                 -> pure p
      NotProjectionLikePragma{}   -> pure p
      DisplayPragma f xs e        -> DisplayPragma f <$> rec xs <*> rec e
    where
      rec :: RecurseExprRecFn m
      rec e = recurseExpr f e

instance ExprLike LHS where
  recurseExpr f (LHS i p) = LHS i <$> recurseExpr f p

instance ExprLike a => ExprLike (LHSCore' a)   where
instance ExprLike a => ExprLike (WithHiding a) where

instance ExprLike SpineLHS where
  recurseExpr f (SpineLHS i x ps) = SpineLHS i x <$> recurseExpr f ps

instance ExprLike Declaration where
  recurseExpr :: forall m. RecurseExprFn m Declaration
  recurseExpr f d =
    case d of
      Axiom a d i mp x e        -> Axiom a d i mp x <$> rec e
      Generalize s i j x e      -> Generalize s i j x <$> rec e
      Field i x e               -> Field i x <$> rec e
      Primitive i x e           -> Primitive i x <$> rec e
      Mutual i ds               -> Mutual i <$> rec ds
      Section i e m tel ds      -> Section i e m <$> rec tel <*> rec ds
      Apply i e m a ci d        -> (\a -> Apply i e m a ci d) <$> rec a
      Import{}                  -> pure d
      Pragma i p                -> Pragma i <$> rec p
      Open{}                    -> pure d
      FunDef i f cs             -> FunDef i f <$> rec cs
      DataSig i er d tel e      -> DataSig i er d <$> rec tel <*> rec e
      DataDef i d uc bs cs      -> DataDef i d uc <$> rec bs <*> rec cs
      RecSig i er r tel e       -> RecSig i er r <$> rec tel <*> rec e
      RecDef i r uc dir bs e ds -> RecDef i r uc dir <$> rec bs <*> rec e <*> rec ds
      PatternSynDef f xs p      -> PatternSynDef f xs <$> rec p
      UnquoteDecl i is xs e     -> UnquoteDecl i is xs <$> rec e
      UnquoteDef i xs e         -> UnquoteDef i xs <$> rec e
      UnquoteData i xs uc j cs e -> UnquoteData i xs uc j cs <$> rec e
      ScopedDecl s ds           -> ScopedDecl s <$> rec ds
      UnfoldingDecl r ds        -> UnfoldingDecl r <$> rec ds
    where
      rec :: RecurseExprRecFn m
      rec e = recurseExpr f e


-- * Getting all declared names
---------------------------------------------------------------------------

type KName = WithKind QName

-- | Extracts "all" names which are declared in a 'Declaration'.
--
-- Includes: local modules and @where@ clauses.
-- Excludes: @open public@, @let@, @with@ function names, extended lambdas.

class DeclaredNames a where
  declaredNames :: Collection KName m => a -> m

  default declaredNames
     :: (Foldable t, DeclaredNames b, t b ~ a)
     => Collection KName m => a -> m
  declaredNames = foldMap declaredNames

instance DeclaredNames a => DeclaredNames [a]
instance DeclaredNames a => DeclaredNames (List1 a)
instance DeclaredNames a => DeclaredNames (Maybe a)
instance DeclaredNames a => DeclaredNames (Arg a)
instance DeclaredNames a => DeclaredNames (Named name a)
instance DeclaredNames a => DeclaredNames (FieldAssignment' a)

instance (DeclaredNames a, DeclaredNames b) => DeclaredNames (Either a b) where
  declaredNames = either declaredNames declaredNames

instance (DeclaredNames a, DeclaredNames b) => DeclaredNames (a,b) where
  declaredNames (a,b) = declaredNames a <> declaredNames b

instance DeclaredNames KName where
  declaredNames = singleton

instance DeclaredNames RecordDirectives where
  declaredNames (RecordDirectives i _ _ c) = kc where
    kc = maybe mempty (singleton . WithKind k) c
    k  = maybe ConName (conKindOfName . rangedThing) i

instance DeclaredNames Declaration where
  declaredNames = \case
      Axiom _ di _ _ q _           -> singleton . (`WithKind` q) $
                                      case defMacro di of
                                        MacroDef    -> MacroName
                                        NotMacroDef -> AxiomName
      Generalize _ _ _ q _         -> singleton (WithKind GeneralizeName q)
      Field _ q _                  -> singleton (WithKind FldName q)
      Primitive _ q _              -> singleton (WithKind PrimName q)
      Mutual _ decls               -> declaredNames decls
      DataSig _ _ q _ _            -> singleton (WithKind DataName q)
      DataDef _ q _ _ decls        -> singleton (WithKind DataName q) <> foldMap con decls
      RecSig _ _ q _ _             -> singleton (WithKind RecName q)
      RecDef _ q _ dir _ _ decls   -> singleton (WithKind RecName q) <> declaredNames dir <> declaredNames decls
      PatternSynDef q _ _          -> singleton (WithKind PatternSynName q)
      UnquoteDecl _ _ qs _         -> fromList $ map (WithKind OtherDefName) qs  -- could be Fun or Axiom
      UnquoteDef _ qs _            -> fromList $ map (WithKind FunName) qs       -- cannot be Axiom
      UnquoteData _ d _ _ cs _     -> singleton (WithKind DataName d) <> (fromList $ map (WithKind ConName) cs) -- singleton _ <> map (WithKind ConName) cs
      FunDef _ q cls               -> singleton (WithKind FunName q) <> declaredNames cls
      ScopedDecl _ decls           -> declaredNames decls
      Section _ _ _ _ decls        -> declaredNames decls
      Pragma _ pragma              -> declaredNames pragma
      Apply{}                      -> mempty
      Import{}                     -> mempty
      Open{}                       -> mempty
      UnfoldingDecl{}              -> mempty
    where
    con = \case
      Axiom _ _ _ _ q _ -> singleton $ WithKind ConName q
      _ -> __IMPOSSIBLE__

instance DeclaredNames Pragma where
  declaredNames = \case
    BuiltinNoDefPragma _b kind x -> singleton $ WithKind kind x
    BuiltinPragma{}           -> mempty
    CompilePragma{}           -> mempty
    RewritePragma{}           -> mempty
    StaticPragma{}            -> mempty
    EtaPragma{}               -> mempty
    InjectivePragma{}         -> mempty
    InlinePragma{}            -> mempty
    NotProjectionLikePragma{} -> mempty
    DisplayPragma{}           -> mempty
    OptionsPragma{}           -> mempty

instance DeclaredNames Clause where
  declaredNames (Clause _ _ rhs decls _) = declaredNames rhs <> declaredNames decls

instance DeclaredNames WhereDeclarations where
  declaredNames (WhereDecls _ _ ds) = declaredNames ds

instance DeclaredNames RHS where
  declaredNames = \case
    RHS _ _                   -> mempty
    AbsurdRHS                 -> mempty
    WithRHS _q _es cls        -> declaredNames cls
    RewriteRHS _qes _ rhs cls -> declaredNames rhs <> declaredNames cls

-- Andreas, 2020-04-13: Migration from Agda.Syntax.Abstract.AllNames
--
-- Since we are not interested in names of extended lambdas, we do not
-- traverse into expression.
--
-- However, we keep this code (originally Agda.Syntax.Abstract.AllNames) around
-- should arise a need to collect extended lambda names.

-- instance (DeclaredNames a, DeclaredNames b, DeclaredNames c) => DeclaredNames (a,b,c) where
--   declaredNames (a,b,c) = declaredNames a <> declaredNames b <> declaredNames c

-- instance DeclaredNames RHS where
--   declaredNames = \case
--     RHS e _                  -> declaredNames e
--     AbsurdRHS{}              -> mempty
--     WithRHS q _ cls          -> singleton (WithKind FunName q) <> declaredNames cls
--     RewriteRHS qes _ rhs cls -> declaredNames (qes, rhs, cls)

-- instance DeclaredNames ModuleName where
--   declaredNames _ = mempty

-- instance (DeclaredNames qn, DeclaredNames e) => DeclaredNames (RewriteEqn' qn p e) where
--   declaredNames = \case
--     Rewrite es    -> declaredNames es
--     Invert qn pes -> declaredNames qn <> declaredNames pes

-- instance DeclaredNames Expr where
--   declaredNames = \case
--     Var{}                 -> mempty
--     Def{}                 -> mempty
--     Proj{}                -> mempty
--     Con{}                 -> mempty
--     Lit{}                 -> mempty
--     QuestionMark{}        -> mempty
--     Underscore{}          -> mempty
--     Dot _ e               -> declaredNames e
--     App _ e1 e2           -> declaredNames e1 <> declaredNames e2
--     WithApp _ e es        -> declaredNames e <> declaredNames es
--     Lam _ b e             -> declaredNames b <> declaredNames e
--     AbsurdLam{}           -> mempty
--     ExtendedLam _ _ q cls -> singleton (WithKind FunName q) <> declaredNames cls
--     Pi _ tel e            -> declaredNames tel <> declaredNames e
--     Generalized s e       -> declaredNames e  -- NOT: fromList (map (WithKind GeneralizeName) $ Set.toList s) <> declaredNames e
--     Fun _ e1 e2           -> declaredNames e1 <> declaredNames e2
--     Set{}                 -> mempty
--     Prop{}                -> mempty
--     Let _ lbs e           -> declaredNames lbs <> declaredNames e
--     Rec _ fields          -> declaredNames fields
--     RecUpdate _ e fs      -> declaredNames e <> declaredNames fs
--     ScopedExpr _ e        -> declaredNames e
--     Quote{}               -> mempty
--     QuoteTerm{}           -> mempty
--     Unquote{}             -> mempty
--     DontCare{}            -> mempty
--     PatternSyn{}          -> mempty
--     Macro{}               -> mempty

-- instance DeclaredNames LamBinding where
--   declaredNames DomainFree{}       = mempty
--   declaredNames (DomainFull binds) = declaredNames binds

-- instance DeclaredNames TypedBinding where
--   declaredNames (TBind _ t _ e) = declaredNames (t, e)
--   declaredNames (TLet _ lbs)    = declaredNames lbs

-- instance DeclaredNames LetBinding where
--   declaredNames (LetBind _ _ _ e1 e2)   = declaredNames e1 <> declaredNames e2
--   declaredNames (LetPatBind _ _ e)      = declaredNames e
--   declaredNames (LetApply _ _ app _ _)  = declaredNames app
--   declaredNames LetOpen{}               = mempty
--   declaredNames (LetDeclaredVariable _) = mempty

-- instance DeclaredNames ModuleApplication where
--   declaredNames (SectionApp bindss _ es) = declaredNames bindss <> declaredNames es
--   declaredNames RecordModuleInstance{}   = mempty
