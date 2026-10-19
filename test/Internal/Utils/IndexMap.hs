-- | Tests for "Agda.Utils.IndexMap".

{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.IndexMap (tests) where

import Agda.Utils.IndexMap (IndexMap)
import qualified Agda.Utils.IndexMap as IndexMap

import Internal.Helpers

instance Arbitrary a => Arbitrary (IndexMap a) where
  arbitrary = do
    xs <- arbitrary
    return (IndexMap.fromList xs)

prop_invariant :: IndexMap Int -> Bool
prop_invariant = IndexMap.invariant

prop_nil :: Property
prop_nil =
  once $
  let m :: IndexMap Int
      m = IndexMap.nil
  in
  IndexMap.invariant m &&
  m == IndexMap.fromList []

prop_snoc :: IndexMap Integer -> Integer -> Bool
prop_snoc m x =
  let m' = IndexMap.snoc m x in
  IndexMap.invariant m' &&
  IndexMap.index 0 m' == x

-- | When a list is appended to a map the last thing in the list
-- should end up at index 0, and so on.

prop_append :: IndexMap Int -> NonNegative Int -> Bool
prop_append m (NonNegative n) =
  let m' = IndexMap.append m [0..n] in
  IndexMap.invariant m' &&
  map (flip IndexMap.index m') (reverse [0..n]) == [0..n]

prop_fromList :: [Integer] -> Bool
prop_fromList xs =
  let m = IndexMap.fromList xs in
  IndexMap.invariant m &&
  m == IndexMap.append IndexMap.nil xs

prop_update :: IndexMap Int -> Int -> Positive Int -> Property
prop_update m x (Positive size) =
  forAll (choose (0, size - 1)) $ \i ->
  let m' = IndexMap.update i x (IndexMap.append m [0 .. size-1]) in
  IndexMap.invariant m' &&
  IndexMap.index i m' == x

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return []

-- | All tests.

tests :: TestTree
tests = testProperties "Internal.Utils.IndexMap" $allProperties
