-- | Free magma: unbalanced binary leaf trees.

module Agda.Utils.LeafTree where

import Agda.Utils.Singleton

data LeafTree a
  = Leaf a
  | Branch (LeafTree a) (LeafTree a)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

instance Semigroup (LeafTree a) where
  (<>) = Branch

instance Singleton a (LeafTree a) where
  singleton = Leaf
