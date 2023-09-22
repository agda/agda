{-# LANGUAGE TemplateHaskell    #-}

module Internal.Utils.Permutation ( tests ) where

import Prelude hiding ((!!))

import Agda.Utils.List ( downFrom, (!!), (!!!) )
import Agda.Utils.Permutation

import Data.Functor
import Data.List ( (\\), nub, sort )
import Data.Maybe

import Internal.Helpers

------------------------------------------------------------------------
-- * Test data generator
------------------------------------------------------------------------

instance Arbitrary Permutation where
  arbitrary = do
    is <- nub . map getNonNegative <$> arbitrary
    NonNegative n <- arbitrary
    return $ Perm (if null is then n else maximum is + n + 1) is

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

data ComposablePermutations = ComposablePermutations Permutation Permutation
  deriving (Eq, Show)

instance Arbitrary ComposablePermutations where
  arbitrary = do
    p2@(Perm n is) <- arbitrary
    let m = length is
    p1 <- Perm m . filter (< m) . map getNonNegative <$> arbitrary
    return $ ComposablePermutations p1 p2

type A = Int

-- | Extend a list by indefinitely many elements.
withStream :: ([a] -> b)  -- ^ Stream function.
           -> [a]         -- ^ Initial segment.
           -> a           -- ^ Default element, appended ad infinitum.
           -> b
withStream k as a = k $ as ++ repeat a

-- | A reference implementation of 'permute'.
slowPermute :: Permutation -> [a] -> [a]
slowPermute (Perm _ is) xs = map (xs !!) is

-- | A variant of 'slowPermute' that does not crash for indices that
-- are out of range.
safePermute :: Permutation -> [a] -> [Maybe a]
safePermute (Perm _ is) xs = map (xs !!!) is

-- | Apply a permutation to a list which might be too short.
--   Silently discard picks that go beyond the list's boundaries.
permutePartial :: Permutation -> [a] -> [a]
permutePartial perm xs =
  catMaybes $ permute perm $ map Just xs ++ repeat Nothing
  -- Note: we have to add @Nothing@s to make @permute@ total.

prop_permute_slowPermute :: Permutation -> [A] -> A -> Bool
prop_permute_slowPermute p = withStream $ \xs ->
  permute p xs == slowPermute p xs

-- | @perm([0..n-1]) == perm@
prop_permute_id_r :: Permutation -> Bool
prop_permute_id_r perm@(Perm n picks) =
  permute perm [0..] == picks

-- | @idP(xs) == xs@
prop_permute_id_l :: Int -> [A] -> A -> Bool
prop_permute_id_l n = withStream $ \ xs ->
  permute (idP n) xs == take n xs

-- | @takeP n perm = perm . take n@
prop_takeP :: Int -> Permutation -> [A] -> A -> Bool
prop_takeP n perm = withStream $ \ xs ->
  permute (takeP n perm) xs == permutePartial perm (take n xs)
  -- Note: we have to add @Nothing@s to make @permute@ total.

-- | @(droppedP perm)(xs) = xs \\ perm(xs)@
prop_droppedP :: Permutation -> [A] -> A -> Bool
prop_droppedP perm@(Perm n _) = withStream $ \ xs -> let xs' = take n xs in
  sort (permute (droppedP perm) xs') == sort (xs' \\ permute perm xs')

-- | @(p1 ∘ p2)(xs) = p1(p2(xs))@
prop_composeP :: ComposablePermutations -> [A] -> A -> Bool
prop_composeP (ComposablePermutations p1 p2) = withStream $ \ xs ->
  permute (composeP p1 p2) xs == permutePartial p1 (permute p2 xs)

prop_flipP :: Permutation -> Bool
prop_flipP p = permPicks (flipP p) == permute p (downFrom $ permRange p)

-- | @p ∘ p⁻¹ ∘ p = p@
prop_invertP_left :: Permutation -> Int -> [A] -> A -> Bool
prop_invertP_left p err = withStream $ \ xs -> let ys = permute p xs in
  permute p (permute (invertP err p) ys) == ys

-- NOT QUITE RIGHT YET:
-- -- | @p⁻1 ∘ p ∘ p⁻¹ = p⁻¹@
-- prop_invertP_right :: Permutation -> Int -> [A] -> A -> Bool
-- prop_invertP_right p err = withStream $ \ xs ->
--   let pinv = invertP err p
--       ys   = permute pinv xs
--   in  permute pinv (permute p ys) == ys

-- | @reverseP p = reverse . p . reverse@
prop_reverseP :: Permutation -> [A] -> A -> Bool
prop_reverseP p@(Perm n _) = withStream $ \ xs0 -> let xs = take n xs0 in
  permute (reverseP p) xs == reverse (permute p (reverse xs))

-- | @permute p . inversePermute p = id@
prop_inversePermute :: Permutation -> [Maybe A] -> Maybe A -> Bool
prop_inversePermute p@(Perm _ is) = withStream $ \ xs0 ->
  let xs = take (length is) xs0
      ys = inversePermute p xs
  in  permute p ys == xs

prop_inversePermute_invertP :: Permutation -> Bool
prop_inversePermute_invertP p =
  inversePermute p (id :: Int -> Int) == safePermute (invertP (-1) p) [(0::Int)..]

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
tests = testProperties "Internal.Utils.Permutation" $allProperties
