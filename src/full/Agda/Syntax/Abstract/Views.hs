{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE PatternGuards             #-}
{-# LANGUAGE TupleSections             #-}

module Agda.Syntax.Abstract.Views where

import Control.Applicative
import Control.Arrow (first)
import Control.Monad.Identity

import Data.Foldable (foldMap)
import Data.Monoid
import Data.Traversable

import Agda.Syntax.Position
import qualified Agda.Syntax.Common as Common
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import Agda.Syntax.Abstract as A
import Agda.Syntax.Info

import Agda.Utils.Either

data AppView = Application Expr [NamedArg Expr]

-- | Gather applications to expose head and spine.
--
--   Note: everything is an application, possibly of itself to 0 arguments
appView :: Expr -> AppView
appView e =
  case e of
    App i e1 arg | Application hd es <- appView e1
                   -> Application hd $ es ++ [arg]
    ScopedExpr _ e -> appView e
    _              -> Application e []

unAppView :: AppView -> Expr
unAppView (Application h es) =
  foldl (App (ExprRange noRange)) h es

-- | Gather top-level 'AsP'atterns to expose underlying pattern.
asView :: A.Pattern -> ([Name], A.Pattern)
asView (A.AsP _ x p) = first (x :) $ asView p
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
unScope e                    = e

-- | Remove 'ScopedExpr' wrappers everywhere.
deepUnScope :: Expr -> Expr
deepUnScope = mapExpr unScope

-- * Traversal

-- | Apply an expression rewriting to every subexpression, inside-out.
--   See "Agda.Syntax.Internal.Generic".
class ExprLike a where
  foldExpr :: Monoid m => (Expr -> m) -> a -> m
  traverseExpr :: (Monad m, Applicative m) => (Expr -> m Expr) -> a -> m a
  mapExpr :: (Expr -> Expr) -> (a -> a)
  mapExpr f = runIdentity . traverseExpr (Identity . f)

instance ExprLike Expr where
  foldExpr f e =
    case e of
      Var{}                -> m
      Def{}                -> m
      Proj{}               -> m
      Con{}                -> m
      PatternSyn{}         -> m
      Lit{}                -> m
      QuestionMark{}       -> m
      Underscore{}         -> m
      App _ e e'           -> m `mappend` fold e `mappend` fold e'
      WithApp _ e es       -> m `mappend` fold e `mappend` fold es
      Lam _ b e            -> m `mappend` fold b `mappend` fold e
      AbsurdLam{}          -> m
      ExtendedLam _ _ _ cs -> m `mappend` fold cs
      Pi _ tel e           -> m `mappend` fold tel `mappend` fold e
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
      App ei e arg            -> f =<< App ei <$> trav e <*> trav arg
      WithApp ei e es         -> f =<< WithApp ei <$> trav e <*> trav es
      Lam ei b e              -> f =<< Lam ei <$> trav b <*> trav e
      AbsurdLam{}             -> f e
      ExtendedLam ei di x cls -> f =<< ExtendedLam ei di x <$> trav cls
      Pi ei tel e             -> f =<< Pi ei <$> trav tel <*> trav e
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

-- | TODO: currently does not go into colors.
instance ExprLike a => ExprLike (Common.Arg c a) where
  foldExpr     = foldMap . foldExpr
  traverseExpr = traverse . traverseExpr

instance ExprLike a => ExprLike (Named x a) where
  foldExpr     = foldMap . foldExpr
  traverseExpr = traverse . traverseExpr

instance ExprLike a => ExprLike [a] where
  foldExpr     = foldMap . foldExpr
  traverseExpr = traverse . traverseExpr

instance ExprLike Assign where
  foldExpr f (Assign _ e) = foldExpr f e
  traverseExpr = exprAssign . traverseExpr

instance (ExprLike a, ExprLike b) => ExprLike (Either a b) where
  foldExpr f = either (foldExpr f) (foldExpr f)
  traverseExpr f = traverseEither (traverseExpr f)
                                  (traverseExpr f)

instance ExprLike ModuleName where
  foldExpr f _ = mempty
  traverseExpr f = pure

instance ExprLike LamBinding where
  foldExpr f e =
    case e of
      DomainFree{}  -> mempty
      DomainFull bs -> foldExpr f bs
  traverseExpr f e =
    case e of
      DomainFree{}  -> return e
      DomainFull bs -> DomainFull <$> traverseExpr f bs

instance ExprLike TypedBindings where
  foldExpr     f (TypedBindings r b) = foldExpr f b
  traverseExpr f (TypedBindings r b) = TypedBindings r <$> traverseExpr f b

instance ExprLike TypedBinding where
  foldExpr f e =
    case e of
      TBind _ _ e  -> foldExpr f e
      TLet _ ds    -> foldExpr f ds
  traverseExpr f e =
    case e of
      TBind r xs e -> TBind r xs <$> traverseExpr f e
      TLet r ds    -> TLet r <$> traverseExpr f ds

instance ExprLike LetBinding where
  foldExpr f e =
    case e of
      LetBind _ _ _ e e' -> fold e `mappend` fold e'
      LetPatBind _ p e   -> fold p `mappend` fold e
      LetApply{}         -> mempty
      LetOpen{}          -> mempty
    where fold e = foldExpr f e

  traverseExpr f e = do
    let trav e = traverseExpr f e
    case e of
      LetBind li ai x e e' -> LetBind li ai x <$> trav e <*> trav e'
      LetPatBind li p e    -> LetPatBind li <$> trav p <*> trav e
      LetApply{}           -> return e
      LetOpen{}            -> return e

-- | TODO: currently does not go into patterns.
instance ExprLike (Pattern' a) where
  foldExpr     f _ = mempty
  traverseExpr f e = return e

-- | TODO: currently does not go into clauses.
instance ExprLike (Clause' a) where
  foldExpr     f _ = mempty
  traverseExpr f e = return e

{- TODO: finish
instance ExprLike (Clause' a) where
  foldExpr f (Clause _ rhs ds) = fold rhs `mappend` fold ds
    where fold e = foldExpr f e
  traverseExpr f (Clause lhs rhs ds) = Clause lhs <$> trav rhs <*> trav ds
    where trav e = traverseExpr f e

instance ExprLike RHS where
  foldExpr f rhs =
    case rhs of
      RHS e                  -> fold e
      AbsurdRHS{}            -> mempty
      WithRHS _ es cs        -> fold es `mappend` fold cs
      RewriteRHS _ es rhs ds -> fold es `mappend` fold rhs `mappend` fold ds
    where fold e = foldExpr f e

  traverseExpr f rhs =
    case rhs of
      RHS e                   -> RHS <$> trav e
      AbsurdRHS{}             -> pure rhs
      WithRHS x es cs         -> WithRHS x <$> trav es <*> trav cs
      RewriteRHS xs es rhs ds -> RewriteRHS xs <$> trav es <*> trav rhs <*> trav ds
    where trav e = traverseExpr f e

instance ExprLike Declaration where
  foldExpr f d =
    case d of
-}
