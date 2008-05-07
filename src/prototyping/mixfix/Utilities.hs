------------------------------------------------------------------------
-- Miscellaneous helper functions
------------------------------------------------------------------------

module Utilities
  ( efficientNub
  , tests
  ) where

import qualified Data.List as List
import Control.Monad
import Data.Function
import Test.QuickCheck

------------------------------------------------------------------------
-- Helper functions

-- | An efficient variant of 'List.nub'.

efficientNub :: Ord a => [a] -> [a]
efficientNub = removeDups . List.sort
  where removeDups = map head . List.group

------------------------------------------------------------------------
-- Code used to test efficientNub

data IgnoreSnd a b = Pair a b
  deriving Show

fst' :: IgnoreSnd a b -> a
fst' (Pair x y) = x

instance (Eq a, Eq b) => Eq (IgnoreSnd a b) where
  (==) = (==) `on` fst'

instance (Ord a, Eq b) => Ord (IgnoreSnd a b) where
  compare = compare `on` fst'

instance (Arbitrary a, Arbitrary b) => Arbitrary (IgnoreSnd a b) where
  arbitrary = liftM2 Pair arbitrary arbitrary

-- | This property tests that 'efficientNub' is equivalent to 'nub',
-- up to a permutation of the output. Note that the property checks
-- that the two functions choose the same representative from every
-- equivalence class.

prop_efficientNub :: [IgnoreSnd Integer Int] -> Property
prop_efficientNub xs =
  classify nonTriv "with non-trivial equivalence classes" $
    efficientNub xs =*= List.sort (List.nub xs)
  where
  xs =*= ys = length xs == length ys && and (zipWith reallyEqual xs ys)
  reallyEqual (Pair x y) (Pair u v) = x == u && y == v

  nonTriv = any ((> 1) . length) $
            map (List.nubBy reallyEqual) $
            List.group $ List.sort xs

------------------------------------------------------------------------
-- All test cases

-- | All tests from this module.

tests = do
  quickCheck prop_efficientNub
