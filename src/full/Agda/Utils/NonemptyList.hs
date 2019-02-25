{-# LANGUAGE DeriveDataTypeable #-}
-- | Nonempty lists.
module Agda.Utils.NonemptyList where

import Control.Monad
import Data.Data (Data)
import Data.Foldable (Foldable)
  -- The toList method of Foldable may do something stupid,
  -- like traversing the list just to build a list again.
import Data.Traversable (Traversable)
import Data.Semigroup
import qualified Data.List as List

infixr 5 :!
data NonemptyList a = (:!) { headNe :: a, tailNe :: [a] }
  deriving (Eq, Ord, Functor, Foldable, Traversable, Data)

instance Semigroup (NonemptyList a) where
  (x :! xs) <> (y :! ys) = x :! xs ++ y : ys

instance Applicative NonemptyList where
  pure x = x :! []
  (<*>) = ap

instance Monad NonemptyList where
  return = pure
  (x :! xs) >>= f = foldr1 (<>) (f x : map f xs)

instance Show a => Show (NonemptyList a) where
  showsPrec _ = showList . toList

-- | Implementing conversion to list manually, since @Foldable.toList@
--   might recurse over the tail and, thus, destroy sharing.
toList :: NonemptyList a -> [a]
toList (x :! xs) = x : xs

-- | Returns the union of the argument lists seen as sets. The order of the
--   elements in the result is not specified. Precondition: arguments contain
--   no duplicates.
unionNe :: Eq a => NonemptyList a -> NonemptyList a -> NonemptyList a
unionNe (x :! xs) (y :! ys) = z :! zs
  where z : zs = List.union (x : xs) (y : ys)

-- | Zip two nonempty lists.
zipWithNe :: (a -> b -> c) -> NonemptyList a -> NonemptyList b -> NonemptyList c
zipWithNe f (x :! xs) (y :! ys) = f x y :! zipWith f xs ys

-- | Zip two nonempty lists.
zipNe :: NonemptyList a -> NonemptyList b -> NonemptyList (a, b)
zipNe = zipWithNe (,)

-- | Case on a list, getting a nonempty list in the cons case.
caseListNe :: [a] -> b -> (NonemptyList a -> b) -> b
caseListNe []       e ne = e
caseListNe (x : xs) e ne = ne (x :! xs)

-- | Case on a list, with list last.
listCaseNe :: b -> (NonemptyList a -> b) -> [a] -> b
listCaseNe e ne xs = caseListNe xs e ne

-- | Check if an element is present in a list.
elemNe :: Eq a => a -> NonemptyList a -> Bool
elemNe y (x :! xs) = elem y (x : xs)
