
module Agda.Syntax.Abstract.Views where

import Prelude hiding (null)

import Control.Applicative ( Const(Const), getConst )
import Control.Monad.Identity
import Control.Monad.State.Strict (State, evalState, get, modify')

import Data.Foldable (foldMap)
import qualified Data.DList as DL
import Data.Void

import Agda.Syntax.Common
import Agda.Syntax.Abstract as A
import Agda.Syntax.Concrete (FieldAssignment', exprFieldA, TacticAttribute')
import Agda.Syntax.Info
import Agda.Syntax.Scope.Base (KindOfName(..), conKindOfName, WithKind(..))
import Agda.Syntax.Position (HasRange, Range'(..), Range, noRange, rangeToPosPair, getRange, contains)

import Agda.Utils.Either
import Agda.Utils.List1 (List1, pattern (:|))
import Agda.Utils.Null
import Agda.Utils.Singleton
import Agda.Utils.Maybe

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

  appView'' = \case
    App i e1 e2
      | Dot _ e2' <- unScope $ namedArg e2
      , Just f <- maybeProjTurnPostfix e2'
      , getHiding e2 == NotHidden -- Jesper, 2018-12-13: postfix projections shouldn't be hidden
      -> (Application f, singleton (defaultNamedArg (i, e1)))
    App i e1 arg | (f, es) <- appView'' e1 ->
      (f, es `DL.snoc` (fmap . fmap) (i,) arg)
    ScopedExpr _ e -> appView'' e
    e              -> (Application e, mempty)

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

-- | Gather top-level 'AsP'atterns to expose underlying pattern.
asView :: A.Pattern -> ([Name], A.Pattern)
asView (A.AsP _ x p)  = (\(asb, p) -> (unBind x : asb, p)) $ asView p
asView p              = ([], p)

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



type RecurseLikeFn   m a = Applicative m => (forall b. ExprLike b => b -> m b -> m b) -> a -> m a
type TraverseLikeFn  m a = (Applicative m, Monad m) => (forall b. ExprLike b => b -> m b) -> a -> m a
type FoldLikeFn      m a = Monoid m => (forall b. ExprLike b => b -> m) -> a -> m
type TraverseLikeRecFn m = forall b. ExprLike b => b -> m b

-- | Apply an expression rewriting to every subexpression, inside-out.
--   See "Agda.Syntax.Internal.Generic".
class HasRange a => ExprLike a where
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

  ctorName :: a -> String
  ctorName _ = "TODO - ctorName"

  recurseExprLike :: RecurseLikeFn m a
  default recurseExprLike
    :: (Traversable t, ExprLike a', a ~ t a', Applicative m)
    => (forall b. ExprLike b => b -> m b -> m b) -> a -> m a
  recurseExprLike g x = g x (traverse (recurseExprLike g) x)

  foldExprLike :: FoldLikeFn m a
  foldExprLike g = getConst . recurseExprLike (\node post -> Const (g node) <* post) 

  traverseExprLike :: TraverseLikeFn m a
  traverseExprLike g = recurseExprLike (\_ post -> post >>= g)

  mapExprLike :: (forall b. ExprLike b => b -> b) -> a -> a
  mapExprLike g = runIdentity . traverseExprLike (pure . g)

  isWrapper :: a -> Bool
  isWrapper _ = False
    
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
      Rec kwr ei bs              -> Rec kwr ei <$> recurse bs
      RecUpdate kwr ei e bs      -> RecUpdate kwr ei <$> recurse e <*> recurse bs
      RecWhere kwr ei bs e       -> RecWhere kwr ei <$> recurse bs <*> recurse e
      RecUpdateWhere k r e ds fs -> RecUpdateWhere k r <$> recurse e <*> recurse ds <*> recurse fs
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
      Var{}                    -> m
      Def'{}                   -> m
      Proj{}                   -> m
      Con{}                    -> m
      PatternSyn{}             -> m
      Macro{}                  -> m
      Lit{}                    -> m
      QuestionMark{}           -> m
      Underscore{}             -> m
      Dot _ e                  -> m `mappend` fold e
      App _ e e'               -> m `mappend` fold e `mappend` fold e'
      WithApp _ e es           -> m `mappend` fold e `mappend` fold es
      Lam _ b e                -> m `mappend` fold b `mappend` fold e
      AbsurdLam{}              -> m
      ExtendedLam _ _ _ _ cs   -> m `mappend` fold cs
      Pi _ tel e               -> m `mappend` fold tel `mappend` fold e
      Generalized _ e          -> m `mappend` fold e
      Fun _ e e'               -> m `mappend` fold e `mappend` fold e'
      Let _ bs e               -> m `mappend` fold bs `mappend` fold e
      Rec _ _ as               -> m `mappend` fold as
      RecUpdate _ _ e as       -> m `mappend` fold e `mappend` fold as
      RecWhere _ _ e as        -> m `mappend` fold e `mappend` fold as
      RecUpdateWhere _ _ e x y -> m `mappend` fold e `mappend` fold x `mappend` fold y
      ScopedExpr _ e           -> m `mappend` fold e
      Quote{}                  -> m
      QuoteTerm{}              -> m
      Unquote{}                -> m
      DontCare e               -> m `mappend` fold e
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
      Rec kwr ei bs              -> f =<< Rec kwr ei <$> trav bs
      RecUpdate kwr ei e bs      -> f =<< RecUpdate kwr ei <$> trav e <*> trav bs
      RecWhere kwr ei e bs       -> f =<< RecWhere kwr ei <$> trav e <*> trav bs
      RecUpdateWhere k r ei e bs -> f =<< RecUpdateWhere k r ei <$> trav e <*> trav bs
      ScopedExpr sc e            -> f =<< ScopedExpr sc <$> trav e
      Quote{}                    -> f e
      QuoteTerm{}                -> f e
      Unquote{}                  -> f e
      DontCare e                 -> f =<< DontCare <$> trav e
      PatternSyn{}               -> f e
      Macro{}                    -> f e


  ctorName e = case e of
   Var _                     -> "Var"
   Def' _ _                  -> "Def'"
   Proj _ _                  -> "Proj"
   Con _                     -> "Con"
   PatternSyn _              -> "PatternSyn"
   Macro _                   -> "Macro"
   Lit _ _                   -> "Lit"
   QuestionMark _ _          -> "QuestionMark"
   Underscore _              -> "Underscore"
   Dot _ _                   -> "Dot"
   App _ _ _                 -> "App"
   WithApp _ _ _             -> "WithApp"
   Lam _ _ _                 -> "Lam"
   AbsurdLam _ _             -> "AbsurdLam"
   ExtendedLam _ _ _ _ _     -> "ExtendedLam"
   Pi _ _ _                  -> "Pi"
   Generalized _ _           -> "Generalized"
   Fun _ _ _                 -> "Fun"
   Let _ _ _                 -> "Let"
   Rec _ _ _                 -> "Rec"
   RecUpdate _ _ _ _         -> "RecUpdate"
   RecWhere _ _ _ _          -> "RecWhere"
   RecUpdateWhere _ _ _ _ _  -> "RecUpdateWhere"
   ScopedExpr _ _            -> "ScopedExpr"
   Quote _                   -> "Quote"
   QuoteTerm _               -> "QuoteTerm"
   Unquote _                 -> "Unquote"
   DontCare _                -> "DontCare"

  isWrapper e = case e of
   ScopedExpr _ _            -> True
   _                         -> False
  recurseExprLike :: forall m. RecurseLikeFn m Expr
  recurseExprLike g e0 = g e0 $ do
    let rec :: TraverseLikeRecFn m
        rec = recurseExprLike g
    case e0 of
      Var{}                      -> pure e0
      Def'{}                     -> pure e0
      Proj{}                     -> pure e0
      Con{}                      -> pure e0
      Lit{}                      -> pure e0
      QuestionMark{}             -> pure e0
      Underscore{}               -> pure e0
      Dot ei e                   -> Dot ei <$> rec e
      App ei e arg               -> App ei <$> rec e <*> rec arg
      WithApp ei e es            -> WithApp ei <$> rec e <*> rec es
      Lam ei b e                 -> Lam ei <$> rec b <*> rec e
      AbsurdLam{}                -> pure e0
      ExtendedLam ei di re x cs  -> ExtendedLam ei di re x <$> rec cs
      Pi ei tel e                -> Pi ei <$> rec tel <*> rec e
      Generalized s e            -> Generalized s <$> rec e
      Fun ei arg e               -> Fun ei <$> rec arg <*> rec e
      Let ei bs e                -> Let ei <$> rec bs <*> rec e
      Rec kwr ei bs              -> Rec kwr ei <$> rec bs
      RecUpdate kwr ei e bs      -> RecUpdate kwr ei <$> rec e <*> rec bs
      RecWhere kwr ei bs e       -> RecWhere kwr ei <$> rec bs <*> rec e
      RecUpdateWhere k r ei e bs -> RecUpdateWhere k r ei <$> rec e <*> rec bs
      ScopedExpr sc e            -> ScopedExpr sc <$> rec e
      Quote{}                    -> pure e0
      QuoteTerm{}                -> pure e0
      Unquote{}                  -> pure e0
      DontCare e                 -> DontCare <$> rec e
      PatternSyn{}               -> pure e0
      Macro{}                    -> pure e0

instance ExprLike a => ExprLike (Arg a) where
  ctorName (Arg _ _) = "Arg"
  isWrapper _ = True
instance ExprLike a => ExprLike (Maybe a) where
  ctorName Nothing  = "Nothing"
  ctorName (Just _) = "Just"

instance ExprLike a => ExprLike (Named x a) where
  ctorName (Named _ _) = "Named"
  isWrapper _ = True
instance ExprLike a => ExprLike (Ranged a) where
  ctorName _ = "Ranged"

instance ExprLike a => ExprLike [a] where
  ctorName []      = "[]"
  ctorName (_:_)   = ":"

instance ExprLike a => ExprLike (List1 a) where
  ctorName (_ :| _) = ":|"

  isWrapper (_ :| []) = True
  isWrapper (_ :| _) = False
  
instance ExprLike a => ExprLike (TacticAttribute' a) where
  ctorName _ = "TacticAttribute'"

instance (ExprLike a, ExprLike b) => ExprLike (a, b) where
  recurseExpr f (x, y) = (,) <$> recurseExpr f x <*> recurseExpr f y

instance ExprLike Void where
  recurseExpr f = absurd
  recurseExprLike _ = absurd

instance ExprLike a => ExprLike (FieldAssignment' a) where
  recurseExpr = exprFieldA . recurseExpr

  recurseExprLike g = exprFieldA (recurseExprLike g)

instance (ExprLike a, ExprLike b) => ExprLike (Either a b) where
  recurseExpr f = traverseEither (recurseExpr f)
                                 (recurseExpr f)

instance ExprLike BindName where
  recurseExpr f = pure
  recurseExprLike g x = g x (pure x)
instance ExprLike ModuleName where
  recurseExpr f = pure
  recurseExprLike g x = g x (pure x)
instance ExprLike QName where
  recurseExpr _ = pure
  recurseExprLike g x = g x (pure x)

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

  recurseExprLike :: forall m. RecurseLikeFn m LamBinding
  recurseExprLike g e =
    g e $ case e of
      DomainFree t x -> DomainFree <$> rec t <*> pure x
      DomainFull bs  -> DomainFull <$> rec bs
    where
      rec :: forall b. ExprLike b => b -> m b
      rec = recurseExprLike g

instance ExprLike GeneralizeTelescope where
  recurseExpr  f (GeneralizeTel s tel) = GeneralizeTel s <$> recurseExpr f tel
  foldExpr     f (GeneralizeTel s tel) = foldExpr f tel
  traverseExpr f (GeneralizeTel s tel) = GeneralizeTel s <$> traverseExpr f tel

  recurseExprLike g (GeneralizeTel s tel) =
    g (GeneralizeTel s tel) (GeneralizeTel s <$> rec tel)
    where rec = recurseExprLike g

instance ExprLike DataDefParams where
  recurseExpr  f (DataDefParams s tel) = DataDefParams s <$> recurseExpr f tel
  foldExpr     f (DataDefParams s tel) = foldExpr f tel
  traverseExpr f (DataDefParams s tel) = DataDefParams s <$> traverseExpr f tel

  recurseExprLike g (DataDefParams s tel) =
    g (DataDefParams s tel) (DataDefParams s <$> rec tel)
    where rec = recurseExprLike g

instance ExprLike TypedBindingInfo where
  recurseExpr f (TypedBindingInfo s t)  = TypedBindingInfo <$> recurseExpr f s <*> pure t
  foldExpr f (TypedBindingInfo s t)     = foldExpr f s
  traverseExpr f (TypedBindingInfo s t) = TypedBindingInfo <$> traverseExpr f s <*> pure t

  recurseExprLike g (TypedBindingInfo s t) =
    g (TypedBindingInfo s t) (TypedBindingInfo <$> rec s <*> pure t)
    where rec = recurseExprLike g

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

  recurseExprLike :: forall m. RecurseLikeFn m TypedBinding
  recurseExprLike g tb =
    g tb $ case tb of
      TBind r t xs e' -> TBind r <$> rec t <*> pure xs <*> rec e'
      TLet  r ds      -> TLet  r <$> rec ds
    where
      rec :: forall b. ExprLike b => b -> m b
      rec = recurseExprLike g
      
instance ExprLike LetBinding where
  recurseExpr :: forall m. RecurseExprFn m LetBinding
  recurseExpr f e = do
    let
      recurse :: RecurseExprRecFn m
      recurse e = recurseExpr f e
    case e of
      LetBind li ai x e e'  -> LetBind li ai x <$> recurse e <*> recurse e'
      LetAxiom li ai x e    -> LetAxiom li ai x <$> recurse e
      LetPatBind li ai p e  -> LetPatBind li ai <$> recurse p <*> recurse e
      LetApply{}            -> pure e
      LetOpen{}             -> pure e

  foldExpr :: forall m. FoldExprFn m LetBinding
  foldExpr f e =
    case e of
      LetBind _ _ _ e e'    -> fold e `mappend` fold e'
      LetAxiom _ _ _ e      -> fold e
      LetPatBind _ _ p e    -> fold p `mappend` fold e
      LetApply{}            -> mempty
      LetOpen{}             -> mempty
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
      LetAxiom li ai x e    -> LetAxiom li ai x <$> trav e
      LetPatBind li ai p e  -> LetPatBind li ai <$> trav p <*> trav e
      LetApply{}            -> pure e
      LetOpen{}             -> pure e

  recurseExprLike :: forall m. RecurseLikeFn m LetBinding
  recurseExprLike g lb = g lb $ case lb of
    LetBind li ai x e e'  -> LetBind li ai x <$> rec e <*> rec e'
    LetAxiom li ai x e    -> LetAxiom li ai x <$> rec e
    LetPatBind li ai p e  -> LetPatBind li ai <$> rec p <*> rec e
    LetApply{}            -> pure lb
    LetOpen{}             -> pure lb
    where rec :: TraverseLikeRecFn m
          rec = recurseExprLike g

instance ExprLike AmbiguousQName where
  -- no Exprs inside; the Expr-focused traversal is a no-op
  recurseExpr _ aq = pure aq

  -- node-level traversal over the AmbiguousQName and its QNames
  recurseExprLike :: forall m. RecurseLikeFn m AmbiguousQName
  recurseExprLike g aq@(AmbQ qs) =
    g aq (AmbQ <$> rec qs)
    where
      rec :: forall b. ExprLike b => b -> m b
      rec = recurseExprLike g
      
instance ExprLike a => ExprLike (Pattern' a) where
  ctorName = \case
    VarP{}        -> "VarP";      ConP{}        -> "ConP"
    ProjP{}       -> "ProjP";     DefP{}        -> "DefP"
    WildP{}       -> "WildP";     AsP{}         -> "AsP"
    DotP{}        -> "DotP";      AbsurdP{}     -> "AbsurdP"
    LitP{}        -> "LitP";      PatternSynP{} -> "PatternSynP"
    RecP{}        -> "RecP";      EqualP{}      -> "EqualP"
    WithP{}       -> "WithP"

  recurseExprLike :: forall m. RecurseLikeFn m (Pattern' a)
  recurseExprLike g p =
    g p $ case p of
      VarP x              -> VarP <$> rec x
      ConP i q as         -> ConP i <$> rec q <*> rec as
      ProjP i o q         -> pure (ProjP i o q)
      DefP i q as         -> DefP i <$> rec q <*> rec as
      WildP i             -> pure (WildP i)
      AsP i n p'          -> AsP i <$> rec n <*> rec p'
      DotP i e            -> DotP i <$> rec e
      AbsurdP i           -> pure (AbsurdP i)
      LitP i l            -> pure (LitP i l)
      PatternSynP i q as  -> PatternSynP i q <$> rec as
      RecP kwr ci fas     -> RecP kwr ci <$> rec fas
      EqualP i es         -> EqualP i <$> rec es
      WithP i p'          -> WithP i <$> rec p'
    where
      rec :: forall b. ExprLike b => b -> m b
      rec = recurseExprLike g
  
instance ExprLike a => ExprLike (Clause' a) where
  recurseExpr :: forall m. RecurseExprFn m (Clause' a)
  recurseExpr f (Clause lhs spats rhs ds ca) = Clause <$> rec lhs <*> pure spats <*> rec rhs <*> rec ds <*> pure ca
    where
      rec :: RecurseExprRecFn m
      rec = recurseExpr f

  recurseExprLike :: forall m. RecurseLikeFn m (Clause' a)
  recurseExprLike g c@(Clause lhs spats rhs ds ca) =
    g c $ Clause <$> rec lhs <*> pure spats <*> rec rhs <*> rec ds <*> pure ca
    where
      rec :: forall b. ExprLike b => b -> m b
      rec = recurseExprLike g

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

  recurseExprLike :: forall m. RecurseLikeFn m RHS
  recurseExprLike g r = g r $ case r of
    RHS e c                    -> RHS <$> rec e <*> pure c
    AbsurdRHS                  -> pure r
    WithRHS x es cs            -> WithRHS x <$> rec es <*> rec cs
    RewriteRHS xes spats rhs ds-> RewriteRHS <$> rec xes <*> pure spats <*> rec rhs <*> rec ds
    where rec :: TraverseLikeRecFn m
          rec = recurseExprLike g

instance (ExprLike qn, ExprLike nm, ExprLike p, ExprLike e) => ExprLike (RewriteEqn' qn nm p e) where
  recurseExpr f = \case
    Rewrite es    -> Rewrite <$> recurseExpr f es
    Invert qn pes -> Invert <$> recurseExpr f qn <*> recurseExpr f pes
    LeftLet pes   -> LeftLet <$> recurseExpr f pes


  recurseExprLike :: forall m. RecurseLikeFn m (RewriteEqn' qn nm p e)
  recurseExprLike g = \case
    re@(Rewrite es)    -> g re $ Rewrite <$> recurseExprLike g es
    iv@(Invert q pes)  -> g iv $ Invert  <$> recurseExprLike g q  <*> recurseExprLike g pes
    ll@(LeftLet pes)   -> g ll $ LeftLet <$> recurseExprLike g pes
    
instance ExprLike WhereDeclarations where
  recurseExpr f (WhereDecls a b c) = WhereDecls a b <$> recurseExpr f c

  recurseExprLike g wd@(WhereDecls a b c) =
    g wd $ WhereDecls a b <$> rec c
    where rec = recurseExprLike g

instance ExprLike ModuleApplication where
  recurseExpr :: forall m. RecurseExprFn m ModuleApplication
  recurseExpr f a =
    case a of
      SectionApp tel m es -> SectionApp <$> rec tel <*> rec m <*> rec es
      RecordModuleInstance{} -> pure a
    where
      rec :: RecurseExprRecFn m
      rec e = recurseExpr f e

  recurseExprLike :: forall m. RecurseLikeFn m ModuleApplication
  recurseExprLike g a =
    g a $ case a of
      SectionApp tel m es     -> SectionApp <$> rec tel <*> rec m <*> rec es
      RecordModuleInstance{}  -> pure a
    where rec :: TraverseLikeRecFn m
          rec = recurseExprLike g

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
      InjectiveForInferencePragma{} -> pure p
      InlinePragma{}              -> pure p
      EtaPragma{}                 -> pure p
      NotProjectionLikePragma{}   -> pure p
      OverlapPragma{}             -> pure p
      DisplayPragma f xs e        -> DisplayPragma f <$> rec xs <*> rec e
    where
      rec :: RecurseExprRecFn m
      rec e = recurseExpr f e

  recurseExprLike :: forall m. RecurseLikeFn m Pragma
  recurseExprLike g p =
    g p $ case p of
      DisplayPragma q xs e -> DisplayPragma q <$> rec xs <*> rec e
      _                    -> pure p
    where rec :: TraverseLikeRecFn m
          rec = recurseExprLike g

instance ExprLike LHS where
  recurseExpr f (LHS i p) = LHS i <$> recurseExpr f p

  recurseExprLike g l@(LHS i p) = g l $ LHS i <$> rec p
    where rec = recurseExprLike g

instance ExprLike a => ExprLike (LHSCore' a)   where
  recurseExprLike :: forall m. RecurseLikeFn m (LHSCore' a)
  recurseExprLike g h =
    g h $ case h of
      LHSHead f ps         -> LHSHead f <$> rec ps
      LHSProj d focus ps   -> LHSProj d <$> rec focus <*> rec ps
      LHSWith h' wps ps    -> LHSWith  <$> rec h'    <*> rec wps <*> rec ps
    where
      rec :: forall b. ExprLike b => b -> m b
      rec = recurseExprLike g
      
instance ExprLike a => ExprLike (WithHiding a) where

instance ExprLike SpineLHS where
  recurseExpr f (SpineLHS i x ps) = SpineLHS i x <$> recurseExpr f ps

  recurseExprLike g s@(SpineLHS i x ps) = g s $ SpineLHS i x <$> rec ps
    where rec = recurseExprLike g

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

  ctorName Axiom{}         = "Axiom"
  ctorName Generalize{}    = "Generalize"
  ctorName Field{}         = "Field"
  ctorName Primitive{}     = "Primitive"
  ctorName Mutual{}        = "Mutual"
  ctorName Section{}       = "Section"
  ctorName Apply{}         = "Apply"
  ctorName Import{}        = "Import"
  ctorName Pragma{}        = "Pragma"
  ctorName Open{}          = "Open"
  ctorName FunDef{}        = "FunDef"
  ctorName DataSig{}       = "DataSig"
  ctorName DataDef{}       = "DataDef"
  ctorName RecSig{}        = "RecSig"
  ctorName RecDef{}        = "RecDef"
  ctorName PatternSynDef{} = "PatternSynDef"
  ctorName UnquoteDecl{}   = "UnquoteDecl"
  ctorName UnquoteDef{}    = "UnquoteDef"
  ctorName UnquoteData{}   = "UnquoteData"
  ctorName ScopedDecl{}    = "ScopedDecl"
  ctorName UnfoldingDecl{} = "UnfoldingDecl"

  recurseExprLike :: forall m. RecurseLikeFn m Declaration
  recurseExprLike g d =
    g d $ case d of
      Axiom a di i mp x e         -> Axiom a di i mp x <$> rec e
      Generalize s i j x e        -> Generalize s i j x <$> rec e
      Field i x e                 -> Field i x <$> rec e
      Primitive i x e             -> Primitive i x <$> rec e
      Mutual i ds                 -> Mutual i <$> rec ds
      Section i e m tel ds        -> Section i e m <$> rec tel <*> rec ds
      Apply i e m a ci d'         -> (\a' -> Apply i e m a' ci d') <$> rec a
      Import{}                    -> pure d
      Pragma i p                  -> Pragma i <$> rec p
      Open{}                      -> pure d
      FunDef i f' cs              -> FunDef i f' <$> rec cs
      DataSig i er d' tel e       -> DataSig i er d' <$> rec tel <*> rec e
      DataDef i d' uc bs cs       -> DataDef i d' uc <$> rec bs <*> rec cs
      RecSig i er r tel e         -> RecSig i er r <$> rec tel <*> rec e
      RecDef i r uc dir bs e ds   -> RecDef i r uc dir <$> rec bs <*> rec e <*> rec ds
      PatternSynDef f' xs p       -> PatternSynDef f' xs <$> rec p
      UnquoteDecl i is xs e       -> UnquoteDecl i is xs <$> rec e
      UnquoteDef i xs e           -> UnquoteDef i xs <$> rec e
      UnquoteData i xs uc j cs e  -> UnquoteData i xs uc j cs <$> rec e
      ScopedDecl s ds             -> ScopedDecl s <$> rec ds
      UnfoldingDecl r ds          -> UnfoldingDecl r <$> rec ds
    where rec :: TraverseLikeRecFn m
          rec = recurseExprLike g

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
    kc = case c of
      NamedRecCon c -> singleton $ WithKind k c
      FreshRecCon{} -> mempty
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
      UnquoteData _ d _ _ cs _     -> singleton (WithKind DataName d) <> fromList (map (WithKind ConName) cs) -- singleton _ <> map (WithKind ConName) cs
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
    InjectiveForInferencePragma{} -> mempty
    InlinePragma{}            -> mempty
    NotProjectionLikePragma{} -> mempty
    DisplayPragma{}           -> mempty
    OptionsPragma{}           -> mempty
    OverlapPragma{}           -> mempty

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

-- instance DeclaredNames ModuleApplication where
--   declaredNames (SectionApp bindss _ es) = declaredNames bindss <> declaredNames es
--   declaredNames RecordModuleInstance{}   = mempty
    

-- | Smallest *strictly* containing expressions (by Range).
-- If several expressions share the same minimal range, return all of them.
findSmallestStrictlyContainingA :: Range -> [Declaration] -> [Expr]
findSmallestStrictlyContainingA = findSmallestContainingWithA Strict

-- | Smallest containing expressions with *non-strict* inclusion (outer may equal target).
-- If several expressions share the same minimal range, return all of them.
findSmallestContainingA :: Range -> [Declaration] -> [Expr]
findSmallestContainingA = findSmallestContainingWithA NonStrict

alignRangeToAbstractDecls :: [Declaration] -> Range -> Range
alignRangeToAbstractDecls dcs r =
  case (findSmallestContainingA r dcs) of
    [] -> noRange
    (x : _) -> getRange x


-- Internal: strictness flag.
data Strictness = Strict | NonStrict

findSmallestContainingWithA :: Strictness -> Range -> [Declaration] -> [Expr]
findSmallestContainingWithA strictness target decls =
  evalState (mapM_ (traverseExpr visit) decls >> get) []
  where
    visit :: Expr -> State [Expr] Expr
    visit e = do
      let er = getRange e
      if contains er target
            then modify' (updateCandidates er e) >> pure e
            else pure e

    -- Containment predicate (strict or non-strict).
    contains :: Range -> Range -> Bool
    contains outer inner =
      case (rangeToPosPair outer, rangeToPosPair inner) of
        (Just (so, eo), Just (si, ei)) ->
          case strictness of
            Strict    -> so <= si && ei <= eo && (so < si || ei < eo)
            NonStrict -> so <= si && ei <= eo
        _ -> False

    -- Update the current best candidate list.
    -- Invariant: list is empty or all Exprs in it share the same minimal range.
    updateCandidates :: Range -> Expr -> [Expr] -> [Expr]
    updateCandidates er e [] = [e]
    updateCandidates er e best@(b:_) =
      let br = expectRange b
      in if rangesEqual er br
           then e : best
           else if isStrictlySmaller er br
                  then [e]
                  else best

    -- Current best range (we only store Exprs in state).
    expectRange :: Expr -> Range
    expectRange x = case getRange x of
      NoRange -> error "findSmallestContainingWithA: internal invariant violated (Expr without range in state)."
      _  -> getRange x 
      

    rangesEqual :: Range -> Range -> Bool
    rangesEqual r1 r2 = rangeToPosPair r1 == rangeToPosPair r2

    -- Prefer containers that are "smaller" (closer to the target).
    -- We use strict inclusion if available; otherwise fall back to length comparison.
    isStrictlySmaller :: Range -> Range -> Bool
    isStrictlySmaller r1 r2 =
      -- r1 inside r2 (hence strictly smaller)
      (case (rangeToPosPair r1, rangeToPosPair r2) of
         (Just (s1,e1), Just (s2,e2)) -> s2 <= s1 && e1 <= e2 && (s2 < s1 || e1 < e2)
         _                            -> False)
      ||
      -- fallback: shorter length
      case (rangeToPosPair r1, rangeToPosPair r2) of
        (Just (s1,e1), Just (s2,e2)) -> (e1 - s1) < (e2 - s2)
        _                            -> False

alignRangeToAbstractExprLikeDecls :: [Declaration] -> Range -> Range
alignRangeToAbstractExprLikeDecls decls target =
  case evalState (mapM_ (traverseExprLike visit) decls >> get) (Nothing :: Maybe Range) of
    Just r  -> r
    Nothing -> noRange
  where
    -- Visit every ExprLike node, and if its range contains the target, update best candidate.
    visit :: forall b. ExprLike b => b -> State (Maybe Range) b
    visit node = do
      let r = getRange node
      when (contains r target) (modify' (updateBest r))
      pure node

    updateBest :: Range -> Maybe Range -> Maybe Range
    updateBest r Nothing   = Just r
    updateBest r (Just br)
      | rangesEqual r br        = Just br
      | isStrictlySmaller r br  = Just r
      | otherwise               = Just br

    rangesEqual :: Range -> Range -> Bool
    rangesEqual r1 r2 = rangeToPosPair r1 == rangeToPosPair r2

    -- Prefer the strictly smaller container; tie-break by span length.
    isStrictlySmaller :: Range -> Range -> Bool
    isStrictlySmaller r1 r2 =
      case (rangeToPosPair r1, rangeToPosPair r2) of
        (Just (s1,e1), Just (s2,e2)) ->
          (s2 <= s1 && e1 <= e2 && (s2 < s1 || e1 < e2)) ||
          ((e1 - s1) < (e2 - s2))
        _ -> False
