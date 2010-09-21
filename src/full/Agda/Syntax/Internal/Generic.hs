{-# LANGUAGE CPP #-}

module Agda.Syntax.Internal.Generic where

import Control.Applicative
import Data.Traversable
import Data.Monoid
import Data.Foldable
import Agda.Syntax.Common
import Agda.Syntax.Internal

#include "../../undefined.h"
import Agda.Utils.Impossible

class TermLike a where
  traverseTerm  :: (Term -> Term) -> a -> a
  traverseTermM :: (Monad m, Applicative m) => (Term -> m Term) -> a -> m a
  foldTerm      :: Monoid m => (Term -> m) -> a -> m

instance TermLike a => TermLike (Arg a) where
  traverseTerm  f = fmap (traverseTerm f)
  traverseTermM f = traverse (traverseTermM f)
  foldTerm f = foldMap (foldTerm f)

instance TermLike a => TermLike [a] where
  traverseTerm f = fmap (traverseTerm f)
  traverseTermM f = traverse (traverseTermM f)
  foldTerm f = foldMap (foldTerm f)

instance (TermLike a, TermLike b) => TermLike (a, b) where
  traverseTerm f (x, y) = (traverseTerm f x, traverseTerm f y)
  traverseTermM f (x, y) = (,) <$> traverseTermM f x <*> traverseTermM f y
  foldTerm f (x, y) = foldTerm f x `mappend` foldTerm f y

instance TermLike a => TermLike (Abs a) where
  traverseTerm f = fmap (traverseTerm f)
  traverseTermM f = traverse (traverseTermM f)
  foldTerm f = foldMap (foldTerm f)

instance TermLike Term where
  traverseTerm f t = case t of
    Var i xs -> f $ Var i $ traverseTerm f xs
    Def c xs -> f $ Def c $ traverseTerm f xs
    Con c xs -> f $ Con c $ traverseTerm f xs
    Lam h b  -> f $ Lam h $ traverseTerm f b
    Pi a b   -> f $ uncurry Pi $ traverseTerm f (a, b)
    Fun a b  -> f $ uncurry Fun $ traverseTerm f (a, b)
    MetaV m xs -> f $ MetaV m $ traverseTerm f xs
    Lit _    -> f t
    Sort _   -> f t
    DontCare -> f t

  traverseTermM f t = case t of
    Var i xs -> f =<< Var i <$> traverseTermM f xs
    Def c xs -> f =<< Def c <$> traverseTermM f xs
    Con c xs -> f =<< Con c <$> traverseTermM f xs
    Lam h b  -> f =<< Lam h <$> traverseTermM f b
    Pi a b   -> f =<< uncurry Pi <$> traverseTermM f (a, b)
    Fun a b  -> f =<< uncurry Fun <$> traverseTermM f (a, b)
    MetaV m xs -> f =<< MetaV m <$> traverseTermM f xs
    Lit _    -> f t
    Sort _   -> f t
    DontCare -> f t

  foldTerm f t = f t `mappend` case t of
    Var i xs   -> foldTerm f xs
    Def c xs   -> foldTerm f xs
    Con c xs   -> foldTerm f xs
    Lam h b    -> foldTerm f b
    Pi a b     -> foldTerm f (a, b)
    Fun a b    -> foldTerm f (a, b)
    MetaV m xs -> foldTerm f xs
    Lit _      -> mempty
    Sort _     -> mempty
    DontCare   -> mempty

instance TermLike Type where
  traverseTerm f (El s t) = El s $ traverseTerm f t
  traverseTermM f (El s t) = El s <$> traverseTermM f t
  foldTerm f (El s t) = foldTerm f t

