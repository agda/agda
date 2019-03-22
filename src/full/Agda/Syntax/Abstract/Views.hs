{-# LANGUAGE CPP                       #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE NoMonoLocalBinds          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Agda.Syntax.Abstract.Views where

import Control.Applicative ( Const(Const), getConst )
import Control.Arrow (first)
import Control.Monad.Identity

import Data.Foldable (foldMap)
import Data.Monoid
import Data.Traversable
import Data.Void

import Agda.Syntax.Position
import Agda.Syntax.Common
import Agda.Syntax.Abstract as A
import Agda.Syntax.Concrete (FieldAssignment', exprFieldA)
import Agda.Syntax.Info
import Agda.Syntax.Scope.Base (emptyScopeInfo)

import Agda.Utils.Either
import Agda.Utils.Lens

data AppView' arg = Application Expr [NamedArg arg]
  deriving (Functor)

type AppView = AppView' Expr

-- | Gather applications to expose head and spine.
--
--   Note: everything is an application, possibly of itself to 0 arguments
appView :: Expr -> AppView
appView = fmap snd . appView'

appView' :: Expr -> AppView' (AppInfo, Expr)
appView' e =
  case e of
    App i e1 e2
      | Dot _ e2' <- unScope $ namedArg e2
      , Just f <- maybeProjTurnPostfix e2'
      , getHiding e2 == NotHidden -- Jesper, 2018-12-13: postfix projections shouldn't be hidden
                   -> Application f [defaultNamedArg (i, e1)]
    App i e1 arg
      | Application hd es <- appView' e1
                   -> Application hd $ es ++ [(fmap . fmap) (i,) arg]
    ScopedExpr _ e -> appView' e
    _              -> Application e []

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

-- | Gather top-level 'AsP'atterns to expose underlying pattern.
asView :: A.Pattern -> ([Name], A.Pattern)
asView (A.AsP _ x p) = first (unBind x :) $ asView p
asView p             = ([], p)

-- | Check whether we are dealing with a universe.
isSet :: Expr -> Bool
isSet (ScopedExpr _ e) = isSet e
isSet (App _ e _)      = isSet e
isSet (Set{})          = True
isSet _                = False

-- | Remove top 'ScopedExpr' wrappers.
unScope :: Expr -> Expr
unScope (ScopedExpr scope e) = unScope e
unScope (QuestionMark i ii)  = QuestionMark (i {metaScope = emptyScopeInfo}) ii
unScope (Underscore i)       = Underscore (i {metaScope = emptyScopeInfo})
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
deepUnscopeDecl (A.ScopedDecl _ ds)              = deepUnscopeDecls ds
deepUnscopeDecl (A.Mutual i ds)                  = [A.Mutual i (deepUnscopeDecls ds)]
deepUnscopeDecl (A.Section i m tel ds)           = [A.Section i m (deepUnscope tel) (deepUnscopeDecls ds)]
deepUnscopeDecl (A.RecDef i x uc ind eta c bs e ds) = [A.RecDef i x uc ind eta c (deepUnscope bs) (deepUnscope e)
                                                                           (deepUnscopeDecls ds)]
deepUnscopeDecl d                                = [deepUnscope d]

-- * Traversal

-- | Apply an expression rewriting to every subexpression, inside-out.
--   See "Agda.Syntax.Internal.Generic".
class ExprLike a where
  -- | The first expression is pre-traversal, the second one post-traversal.
  recurseExpr :: (Applicative m) => (Expr -> m Expr -> m Expr) -> a -> m a
  default recurseExpr :: (Traversable f, ExprLike a', a ~ f a', Applicative m)
                      => (Expr -> m Expr -> m Expr) -> a -> m a
  recurseExpr = traverse . recurseExpr

  foldExpr :: Monoid m => (Expr -> m) -> a -> m
  foldExpr f = getConst . recurseExpr (\ pre post -> Const (f pre) <* post)

  traverseExpr :: (Applicative m, Monad m) => (Expr -> m Expr) -> a -> m a
  traverseExpr f = recurseExpr (\ pre post -> f =<< post)

  mapExpr :: (Expr -> Expr) -> (a -> a)
  mapExpr f = runIdentity . traverseExpr (Identity . f)

instance ExprLike Expr where
  recurseExpr f e0 = f e0 $ do
    let recurse e = recurseExpr f e
    case e0 of
      Var{}                   -> pure e0
      Def{}                   -> pure e0
      Proj{}                  -> pure e0
      Con{}                   -> pure e0
      Lit{}                   -> pure e0
      QuestionMark{}          -> pure e0
      Underscore{}            -> pure e0
      Dot ei e                -> Dot ei <$> recurse e
      App ei e arg            -> App ei <$> recurse e <*> recurse arg
      WithApp ei e es         -> WithApp ei <$> recurse e <*> recurse es
      Lam ei b e              -> Lam ei <$> recurse b <*> recurse e
      AbsurdLam{}             -> pure e0
      ExtendedLam ei di x cls -> ExtendedLam ei di x <$> recurse cls
      Pi ei tel e             -> Pi ei <$> recurse tel <*> recurse e
      Generalized  s e        -> Generalized s <$> recurse e
      Fun ei arg e            -> Fun ei <$> recurse arg <*> recurse e
      Set{}                   -> pure e0
      Prop{}                  -> pure e0
      Let ei bs e             -> Let ei <$> recurse bs <*> recurse e
      ETel tel                -> ETel <$> recurse tel
      Rec ei bs               -> Rec ei <$> recurse bs
      RecUpdate ei e bs       -> RecUpdate ei <$> recurse e <*> recurse bs
      ScopedExpr sc e         -> ScopedExpr sc <$> recurse e
      QuoteGoal ei n e        -> QuoteGoal ei n <$> recurse e
      QuoteContext ei         -> pure e0
      Quote{}                 -> pure e0
      QuoteTerm{}             -> pure e0
      Unquote{}               -> pure e0
      DontCare e              -> DontCare <$> recurse e
      PatternSyn{}            -> pure e0
      Tactic ei e xs ys       -> Tactic ei <$> recurse e <*> recurse xs <*> recurse ys
      Macro{}                 -> pure e0

  foldExpr f e =
    case e of
      Var{}                -> m
      Def{}                -> m
      Proj{}               -> m
      Con{}                -> m
      PatternSyn{}         -> m
      Macro{}              -> m
      Lit{}                -> m
      QuestionMark{}       -> m
      Underscore{}         -> m
      Dot _ e              -> m `mappend` fold e
      App _ e e'           -> m `mappend` fold e `mappend` fold e'
      WithApp _ e es       -> m `mappend` fold e `mappend` fold es
      Lam _ b e            -> m `mappend` fold b `mappend` fold e
      AbsurdLam{}          -> m
      ExtendedLam _ _ _ cs -> m `mappend` fold cs
      Pi _ tel e           -> m `mappend` fold tel `mappend` fold e
      Generalized _ e      -> m `mappend` fold e
      Fun _ e e'           -> m `mappend` fold e `mappend` fold e'
      Set{}                -> m
      Prop{}               -> m
      Let _ bs e           -> m `mappend` fold bs `mappend` fold e
      ETel tel             -> m `mappend` fold tel
      Rec _ as             -> m `mappend` fold as
      RecUpdate _ e as     -> m `mappend` fold e `mappend` fold as
      ScopedExpr _ e       -> m `mappend` fold e
      QuoteGoal _ _ e      -> m `mappend` fold e
      QuoteContext _       -> m
      Quote{}              -> m
      QuoteTerm{}          -> m
      Unquote{}            -> m
      Tactic _ e xs ys     -> m `mappend` fold e `mappend` fold xs `mappend` fold ys
      DontCare e           -> m `mappend` fold e
   where
     m    = f e
     fold = foldExpr f

  traverseExpr f e = do
    let trav e = traverseExpr f e
    case e of
      Var{}                   -> f e
      Def{}                   -> f e
      Proj{}                  -> f e
      Con{}                   -> f e
      Lit{}                   -> f e
      QuestionMark{}          -> f e
      Underscore{}            -> f e
      Dot ei e                -> f =<< Dot ei <$> trav e
      App ei e arg            -> f =<< App ei <$> trav e <*> trav arg
      WithApp ei e es         -> f =<< WithApp ei <$> trav e <*> trav es
      Lam ei b e              -> f =<< Lam ei <$> trav b <*> trav e
      AbsurdLam{}             -> f e
      ExtendedLam ei di x cls -> f =<< ExtendedLam ei di x <$> trav cls
      Pi ei tel e             -> f =<< Pi ei <$> trav tel <*> trav e
      Generalized s e         -> f =<< Generalized s <$> trav e
      Fun ei arg e            -> f =<< Fun ei <$> trav arg <*> trav e
      Set{}                   -> f e
      Prop{}                  -> f e
      Let ei bs e             -> f =<< Let ei <$> trav bs <*> trav e
      ETel tel                -> f =<< ETel <$> trav tel
      Rec ei bs               -> f =<< Rec ei <$> trav bs
      RecUpdate ei e bs       -> f =<< RecUpdate ei <$> trav e <*> trav bs
      ScopedExpr sc e         -> f =<< ScopedExpr sc <$> trav e
      QuoteGoal ei n e        -> f =<< QuoteGoal ei n <$> trav e
      QuoteContext{}          -> f e
      Quote{}                 -> f e
      QuoteTerm{}             -> f e
      Unquote{}               -> f e
      Tactic ei e xs ys       -> f =<< Tactic ei <$> trav e <*> trav xs <*> trav ys
      DontCare e              -> f =<< DontCare <$> trav e
      PatternSyn{}            -> f e
      Macro{}                 -> f e

instance ExprLike a => ExprLike (Arg a)     where
instance ExprLike a => ExprLike (Named x a) where
instance ExprLike a => ExprLike [a]         where

instance (ExprLike a, ExprLike b) => ExprLike (a, b) where
  recurseExpr f (x, y) = (,) <$> recurseExpr f x <*> recurseExpr f y

instance ExprLike Void where
  recurseExpr f = absurd

instance ExprLike a => ExprLike (FieldAssignment' a) where
  recurseExpr = exprFieldA . recurseExpr

instance (ExprLike a, ExprLike b) => ExprLike (Either a b) where
  recurseExpr f = traverseEither (recurseExpr f)
                                 (recurseExpr f)

instance ExprLike ModuleName where
  recurseExpr f = pure

instance ExprLike QName where
  recurseExpr _ = pure

instance ExprLike LamBinding where
  recurseExpr f e =
    case e of
      DomainFree{}  -> pure e
      DomainFull bs -> DomainFull <$> recurseExpr f bs
  foldExpr f e =
    case e of
      DomainFree{}  -> mempty
      DomainFull bs -> foldExpr f bs
  traverseExpr f e =
    case e of
      DomainFree{}  -> pure e
      DomainFull bs -> DomainFull <$> traverseExpr f bs

instance ExprLike GeneralizeTelescope where
  recurseExpr  f (GeneralizeTel s tel) = GeneralizeTel s <$> recurseExpr f tel
  foldExpr     f (GeneralizeTel s tel) = foldExpr f tel
  traverseExpr f (GeneralizeTel s tel) = GeneralizeTel s <$> traverseExpr f tel

instance ExprLike DataDefParams where
  recurseExpr  f (DataDefParams s tel) = DataDefParams s <$> recurseExpr f tel
  foldExpr     f (DataDefParams s tel) = foldExpr f tel
  traverseExpr f (DataDefParams s tel) = DataDefParams s <$> traverseExpr f tel

instance ExprLike TypedBinding where
  recurseExpr f e =
    case e of
      TBind r xs e -> TBind r xs <$> recurseExpr f e
      TLet r ds    -> TLet r <$> recurseExpr f ds
  foldExpr f e =
    case e of
      TBind _ _ e  -> foldExpr f e
      TLet _ ds    -> foldExpr f ds
  traverseExpr f e =
    case e of
      TBind r xs e -> TBind r xs <$> traverseExpr f e
      TLet r ds    -> TLet r <$> traverseExpr f ds

instance ExprLike LetBinding where
  recurseExpr f e = do
    let recurse e = recurseExpr f e
    case e of
      LetBind li ai x e e'  -> LetBind li ai x <$> recurse e <*> recurse e'
      LetPatBind li p e     -> LetPatBind li <$> recurse p <*> recurse e
      LetApply{}            -> pure e
      LetOpen{}             -> pure e
      LetDeclaredVariable _ -> pure e

  foldExpr f e =
    case e of
      LetBind _ _ _ e e'    -> fold e `mappend` fold e'
      LetPatBind _ p e      -> fold p `mappend` fold e
      LetApply{}            -> mempty
      LetOpen{}             -> mempty
      LetDeclaredVariable _ -> mempty
    where fold e = foldExpr f e

  traverseExpr f e = do
    let trav e = traverseExpr f e
    case e of
      LetBind li ai x e e'  -> LetBind li ai x <$> trav e <*> trav e'
      LetPatBind li p e     -> LetPatBind li <$> trav p <*> trav e
      LetApply{}            -> pure e
      LetOpen{}             -> pure e
      LetDeclaredVariable _ -> pure e

instance ExprLike a => ExprLike (Pattern' a) where

instance ExprLike a => ExprLike (Clause' a) where
  recurseExpr f (Clause lhs spats rhs ds ca) = Clause <$> rec lhs <*> pure spats <*> rec rhs <*> rec ds <*> pure ca
    where rec = recurseExpr f

instance ExprLike RHS where
  recurseExpr f rhs =
    case rhs of
      RHS e c                 -> RHS <$> rec e <*> pure c
      AbsurdRHS{}             -> pure rhs
      WithRHS x es cs         -> WithRHS x <$> rec es <*> rec cs
      RewriteRHS xes spats rhs ds -> RewriteRHS <$> rec xes <*> pure spats <*> rec rhs <*> rec ds
    where rec e = recurseExpr f e

instance ExprLike WhereDeclarations where
  recurseExpr f (WhereDecls a b) = WhereDecls a <$> recurseExpr f b

instance ExprLike ModuleApplication where
  recurseExpr f a =
    case a of
      SectionApp tel m es -> SectionApp <$> rec tel <*> rec m <*> rec es
      RecordModuleInstance{} -> pure a
    where rec e = recurseExpr f e

instance ExprLike Pragma where
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
      DisplayPragma f xs e        -> DisplayPragma f <$> rec xs <*> rec e
    where rec e = recurseExpr f e

instance ExprLike LHS where
  recurseExpr f (LHS i p) = LHS i <$> recurseExpr f p

instance ExprLike a => ExprLike (LHSCore' a) where

instance ExprLike SpineLHS where
  recurseExpr f (SpineLHS i x ps) = SpineLHS i x <$> recurseExpr f ps

instance ExprLike Declaration where
  recurseExpr f d =
    case d of
      Axiom a d i mp x e        -> Axiom a d i mp x <$> rec e
      Generalize s i j x e      -> Generalize s i j x <$> rec e
      Field i x e               -> Field i x <$> rec e
      Primitive i x e           -> Primitive i x <$> rec e
      Mutual i ds               -> Mutual i <$> rec ds
      Section i m tel ds        -> Section i m <$> rec tel <*> rec ds
      Apply i m a ci d          -> (\ a -> Apply i m a ci d) <$> rec a
      Import{}                  -> pure d
      Pragma i p                -> Pragma i <$> rec p
      Open{}                    -> pure d
      FunDef i f d cs           -> FunDef i f d <$> rec cs
      DataSig i d tel e         -> DataSig i d <$> rec tel <*> rec e
      DataDef i d uc bs cs      -> DataDef i d uc <$> rec bs <*> rec cs
      RecSig i r tel e          -> RecSig i r <$> rec tel <*> rec e
      RecDef i r uc n co c bs e ds -> RecDef i r uc n co c <$> rec bs <*> rec e <*> rec ds
      PatternSynDef f xs p      -> PatternSynDef f xs <$> rec p
      UnquoteDecl i is xs e     -> UnquoteDecl i is xs <$> rec e
      UnquoteDef i xs e         -> UnquoteDef i xs <$> rec e
      ScopedDecl s ds           -> ScopedDecl s <$> rec ds
    where rec e = recurseExpr f e
