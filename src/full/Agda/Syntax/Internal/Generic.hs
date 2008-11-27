{-# LANGUAGE CPP #-}

module Agda.Syntax.Internal.Generic where

import Control.Applicative
import Data.Traversable
import Agda.Syntax.Common
import Agda.Syntax.Internal

#include "../../undefined.h"
import Agda.Utils.Impossible

class TermLike a where
  traverseTerm  :: (Term -> Term) -> a -> a
  -- traverseTermM :: (Applicative m, Monad m) => (Term -> m Term) -> a -> m a

instance TermLike a => TermLike (Arg a) where
  traverseTerm f = fmap (traverseTerm f)
  -- traverseTermM f = traverse (traverseTermM f)

instance TermLike a => TermLike [a] where
  traverseTerm f = fmap (traverseTerm f)

instance (TermLike a, TermLike b) => TermLike (a, b) where
  traverseTerm f (x, y) = (traverseTerm f x, traverseTerm f y)

instance TermLike a => TermLike (Abs a) where
  traverseTerm f (Abs s x) = Abs s (traverseTerm f x)

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

instance TermLike Type where
  traverseTerm f (El s t) = El s $ traverseTerm f t

