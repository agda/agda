{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module InternalTests.Utils.List ( tests ) where

import Agda.Utils.List

import Data.Function
import Data.List

import InternalTests.Helpers

------------------------------------------------------------------------------

-- Trivial:
-- prop_initLast_nil       = initLast [] == Nothing

prop_initLast_cons a as = initLast xs == Just (init xs, last xs)
  where xs = a:as

spec_updateHead f as = let (bs, cs) = splitAt 1 as in map f bs ++ cs
prop_updateHead f as = updateHead f as == spec_updateHead f as

spec_updateLast f as = let (bs, cs) = splitAt (length as - 1) as in bs ++ map f cs
prop_updateLast f as = updateLast f as == spec_updateLast f as

spec_updateAt n f as = let (bs, cs) = splitAt n as in bs ++ updateHead f cs
prop_updateAt (NonNegative n) f as = updateAt n f as == spec_updateAt n f as

prop_mapMaybeAndRest_Nothing as = mapMaybeAndRest (const Nothing) as == ([] :: [Int],as)
prop_mapMaybeAndRest_Just    as = mapMaybeAndRest Just            as == (as,[])

prop_chop_intercalate :: Property
prop_chop_intercalate =
  forAllShrink (choose (0, 4 :: Int))          shrink $ \ d ->
  forAllShrink (listOf (choose (0, 4 :: Int))) shrink $ \ xs ->
  xs === intercalate [d] (chopWhen (== d) xs)

prop_distinct_fastDistinct :: [Integer] -> Bool
prop_distinct_fastDistinct xs = distinct xs == fastDistinct xs

prop_groupBy' :: (Bool -> Bool -> Bool) -> [Bool] -> Property
prop_groupBy' p xs =
  classify (length xs - length gs >= 3) "interesting" $
    concat gs == xs
    &&
    and [not (null zs) | zs <- gs]
    &&
    and [and (pairInitTail zs zs) | zs <- gs]
    &&
    (null gs || not (or (pairInitTail (map last gs) (map head gs))))
  where gs = groupBy' p xs
        pairInitTail xs ys = zipWith p (init xs) (tail ys)

prop_genericElemIndex :: Integer -> [Integer] -> Property
prop_genericElemIndex x xs =
  classify (x `elem` xs) "members" $
    genericElemIndex x xs == elemIndex x xs

prop_zipWith' :: (Integer -> Integer -> Integer) -> Property
prop_zipWith' f =
  forAll natural $ \n ->
    forAll (two $ vector n) $ \(xs, ys) ->
      zipWith' f xs ys == Just (zipWith f xs ys)

prop_nubOn :: (Integer -> Integer) -> [Integer] -> Bool
prop_nubOn f xs = nubOn f xs == nubBy ((==) `on` f) xs

prop_uniqOn1 :: (Integer -> Integer) -> [Integer] -> Bool
prop_uniqOn1 f xs' =
  or [ uniqOn f xs == nubBy ((==) `on` f) ys
     | ys <- permutations xs
     ]
  where
  xs = take 5 xs'

  permutations []       = [[]]
  permutations (x : xs) =
    [ ys1 ++ x : ys2
    | ys <- permutations xs
    , n  <- [0..length ys]
    , let (ys1, ys2) = splitAt n ys
    ]

prop_uniqOn2 :: (Integer -> Integer) -> [Integer] -> Bool
prop_uniqOn2 f xs =
  sortBy (compare `on` f) (uniqOn f xs) == uniqOn f xs

prop_commonPrefix :: [Integer] -> [Integer] -> [Integer] -> Bool
prop_commonPrefix xs ys zs =
  and [ isPrefixOf zs zs'
      , isPrefixOf zs' (zs ++ xs)
      , isPrefixOf zs' (zs ++ ys) ]
  where
    zs' = commonPrefix (zs ++ xs) (zs ++ ys)

prop_commonSuffix :: [Integer] -> [Integer] -> [Integer] -> Bool
prop_commonSuffix xs ys zs =
  and [ isSuffixOf zs zs'
      , isSuffixOf zs' (xs ++ zs)
      , isSuffixOf zs' (ys ++ zs) ]
  where
    zs' = commonSuffix (xs ++ zs) (ys ++ zs)

prop_editDistance :: Property
prop_editDistance =
  forAllShrink (choose (0, 10)) shrink $ \ n ->
  forAllShrink (choose (0, 10)) shrink $ \ m ->
  forAllShrink (vector n) shrink $ \ xs ->
  forAllShrink (vector m) shrink $ \ ys ->
  editDistanceSpec xs ys == editDistance xs (ys :: [Integer])

-- Hack to make $quickCheckAll work under ghc-7.8
return []

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = do
  putStrLn "InternalTests.Utils.List"
  $quickCheckAll
