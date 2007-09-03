-- | Some utility functions.

module Termination.Utilities
  ( extractNthElement
  , groupOn
  , on
  , tests
  ) where

import Test.QuickCheck
import Data.List

-- | @'extractNthElement' n xs@ gives the @n@-th element in @xs@
-- (counting from 0), plus the remaining elements (preserving order).

extractNthElement :: Integral i => i -> [a] -> (a, [a])
extractNthElement n xs = (elem, left ++ right)
  where
  (left, elem : right) = genericSplitAt n xs

prop_extractNthElement :: Integer -> [Integer] -> Property
prop_extractNthElement n xs =
  0 <= n && n < genericLength xs ==>
    genericTake n rest ++ [elem] ++ genericDrop n rest == xs
  where (elem, rest) = extractNthElement n xs

-- | @'groupOn' f = 'groupBy' (('==') \`on\` f) '.' 'sortBy' ('compare' \`on\` f)@.

groupOn :: Ord b => (a -> b) -> [a] -> [[a]]
groupOn f = groupBy ((==) `on` f) . sortBy (compare `on` f)

-- | @(*) \`on\` f = \\x y -> f x * f y@.

on :: (b -> b -> c) -> (a -> b) -> a -> a -> c
(*) `on` f = \x y -> f x * f y

------------------------------------------------------------------------
-- All tests

tests = do
  quickCheck prop_extractNthElement
