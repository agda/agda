------------------------------------------------------------------------
-- | Utilities for the 'Either' type
------------------------------------------------------------------------

module Utils.Either
  ( rights
  , tests
  ) where

import Control.Arrow
import Test.QuickCheck

-- | Extracts the right elements from the list.

rights :: [Either a b] -> [b]
rights []             = []
rights (Right x : xs) = x : rights xs
rights (Left _  : xs) = rights xs

prop_rights1 :: [Either Bool Integer] -> Bool
prop_rights1 xs =
  rights xs == concatMap (const [] ||| \x -> [x]) xs

prop_rights2 xs =
  rights (map Right xs :: [Either Bool Integer]) == xs

-- | Extracts the left elements from the list.

lefts :: [Either a b] -> [a]
lefts []             = []
lefts (Right _ : xs) = lefts xs
lefts (Left x  : xs) = x : lefts xs

prop_lefts_rights :: [Either Bool Integer] -> Bool
prop_lefts_rights xs =
  length (lefts xs) + length (rights xs) == length xs

------------------------------------------------------------------------
-- All tests

tests = do
  quickCheck prop_rights1
  quickCheck prop_rights2
  quickCheck prop_lefts_rights
