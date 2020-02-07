{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.Bag ( tests ) where

import Agda.Utils.Bag

import Data.Functor.Identity
import qualified Data.List as List
import qualified Data.Set as Set

import Prelude hiding ( map )

import Internal.Helpers

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

instance (Ord a, Arbitrary a) => Arbitrary (Bag a) where
  arbitrary = fromList <$> arbitrary

prop_count_empty :: Ord a => a -> Bool
prop_count_empty a = count a empty == 0

prop_count_singleton :: Ord a => a -> Bool
prop_count_singleton a = count a (singleton a) == 1

prop_count_insert :: Ord a => a -> Bag a -> Bool
prop_count_insert a b = count a (insert a b) == 1 + count a b

prop_size_union :: Ord a => Bag a -> Bag a -> Bool
prop_size_union b c = size (b `union` c) == size b + size c

prop_size_fromList :: Ord a => [a] -> Bool
prop_size_fromList l = size (fromList l) == length l

prop_fromList_toList :: Ord a => Bag a -> Bool
prop_fromList_toList b = fromList (toList b) == b

prop_toList_fromList :: Ord a => [a] -> Bool
prop_toList_fromList l = toList (fromList l) == List.sort l

prop_keys_fromList :: Ord a => [a] -> Bool
prop_keys_fromList l = keys (fromList l) == Set.toList (Set.fromList l)

prop_nonempty_groups :: Bag a -> Bool
prop_nonempty_groups b = all (not . List.null) $ groups b

prop_map_id :: Ord a => Bag a -> Bool
prop_map_id b = map id b == b

prop_map_compose :: (Ord b, Ord c) =>
                    (b -> c) -> (a -> b) -> Bag a -> Bool
prop_map_compose f g b = map f (map g b) == map (f . g) b

prop_traverse_id :: Ord a => Bag a -> Bool
prop_traverse_id b = traverse' Identity b == Identity b

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'allProperties'.
--
-- Using 'allProperties' is convenient and superior to the manual
-- enumeration of tests, since the name of the property is added
-- automatically.

tests :: TestTree
tests = testProperties "Internal.Utils.Bag" $allProperties
