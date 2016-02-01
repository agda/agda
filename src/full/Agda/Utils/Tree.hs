-- ASR (25 January 2016): Not used.

-- {-# LANGUAGE DeriveFoldable #-}
-- {-# LANGUAGE DeriveFunctor #-}
-- {-# LANGUAGE DeriveTraversable #-}

-- module Agda.Utils.Tree where

-- import Data.Monoid
-- import Data.Foldable
-- import Data.Traversable

-- import Agda.Utils.Pointed

-- -- | Leaf-labelled trees (free monoids).
-- data Tree a = Empty | Leaf a | Node (Tree a) (Tree a)
--   deriving (Eq, Ord, Functor, Foldable, Traversable)

-- instance Pointed Tree where
--   point = Leaf

-- instance Monoid (Tree a) where
--   mempty  = Empty
--   mappend = Node

-- -- | Initiality.
-- flatten :: (Pointed f, Monoid (f a)) => Tree a -> f a
-- flatten = foldMap point

-- -- The properties cannot be stated in full generality
-- -- because of type ambiguities.
-- propFlattenEmpty    = flatten Empty == ([] :: [Int])
-- propFlattenLeaf a   = flatten (Leaf a) == [a]
-- propFlattenNode l r = flatten (Node l r) == (flatten l) ++ (flatten r)
