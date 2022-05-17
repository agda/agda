{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP             #-}

#if  __GLASGOW_HASKELL__ > 800
{-# OPTIONS_GHC -Wno-error=missing-signatures #-}
#endif
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Internal.Utils.List ( tests ) where

import Agda.Utils.List

import Data.Either (partitionEithers)
import Data.Function
import Data.List ( (\\), elemIndex, intercalate, isPrefixOf, isSuffixOf, nub, nubBy, sort, sortBy )

import Internal.Helpers

------------------------------------------------------------------------------

prop_last2 a b as = last2 (a:b:as) == toPair (drop (length as) $ a:b:as)
  where
  toPair [x,y] = Just (x,y)
  toPair _     = Nothing

prop_dropEnd n as = dropEnd n as == reverse (drop n (reverse as))

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

prop_spanEnd_split   p xs = let (ys, zs) = spanEnd p xs in xs == ys ++ zs
prop_spanEnd_holds   p xs = let (ys, zs) = spanEnd p xs in all p zs
prop_spanEnd_maximal p xs = let (ys, zs) = spanEnd p xs in maybe True (not . p) (lastMaybe ys)

prop_partitionMaybe :: (Int -> Maybe Bool) -> [Int] -> Bool
prop_partitionMaybe f as = partitionMaybe f as == partitionEithers (map f' as)
  where f' a = maybe (Left a) Right $ f a

prop_mapMaybeAndRest_Nothing as = mapMaybeAndRest (const Nothing) as == ([] :: [Int],as)
prop_mapMaybeAndRest_Just    as = mapMaybeAndRest Just            as == (as,[])

prop_stripSuffix_sound    suf xs  = maybe True (\ pre -> xs == pre ++ suf) $ stripSuffix suf xs
prop_stripSuffix_complete pre suf = stripSuffix suf (pre ++ suf) == Just pre

prop_stripReversedSuffix_sound    rsuf xs  = maybe True (\ pre -> xs == pre ++ reverse rsuf) $ stripReversedSuffix rsuf xs
prop_stripReversedSuffix_complete pre rsuf = stripReversedSuffix rsuf (pre ++ reverse rsuf) == Just pre

prop_chop_intercalate :: Property
prop_chop_intercalate =
  forAllShrink (choose (0, 4 :: Int))          shrink $ \ d ->
  forAllShrink (listOf (choose (0, 4 :: Int))) shrink $ \ xs ->
  xs === intercalate [d] (chopWhen (== d) xs)

prop_distinct_fastDistinct :: [Integer] -> Bool
prop_distinct_fastDistinct xs = distinct xs == fastDistinct xs

-- To test duplicates, we distinguish them with a decoration by some small natural number.

data Decorate a = Decorate (Positive (Small Int)) a
  deriving (Show)

instance Eq a => Eq (Decorate a) where
  (==) = (==) `on` (\ (Decorate _ a) -> a)

instance Ord a => Ord (Decorate a) where
  compare = compare `on` (\ (Decorate _ a) -> a)

instance Arbitrary a => Arbitrary (Decorate a) where
  arbitrary = Decorate <$> arbitrary <*> arbitrary

prop_allDuplicates :: [Decorate (Positive Int)] -> Bool
prop_allDuplicates xs = allDuplicates xs `sameList` sort (xs \\ nub xs)
  where
  sameList xs ys = and $ zipWith same xs ys
  same (Decorate i a) (Decorate j b) = i == j && a == b

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

-- | Defining property of zipWithKeepRest
prop_zipWithKeepRest f as bs =
  zipWithKeepRest f as bs == zipWith f as bs ++ drop (length as) bs

-- Redundant properties of zipWithKeepRest:

-- | The second list does not get shorter.
prop_zipWithKeepRest_length f as bs =
  length (zipWithKeepRest f as bs) == length bs

-- | If the first list is at least as long as the second,
--   'zipWithKeepRest' behaves like 'zipWith'.
prop_zipWithKeepRest_first_longer f as bs =
  let cs = as ++ bs in
  zipWithKeepRest f cs bs == zipWith f cs bs

-- | The rest of the second list is unchanged.
prop_zipWithKeepRest_rest_unchanged f as bs =
  drop (length as) (zipWithKeepRest f as bs) == drop (length as) bs

-- | The initial part is like in zipWith.
prop_zipWithKeepRest_init_zipWith f as bs =
  take (length as) (zipWithKeepRest f as bs) ==
  take (length as) (zipWith         f as bs)



prop_nubOn :: (Integer -> Integer) -> [Integer] -> Bool
prop_nubOn f xs = nubOn f xs == nubBy ((==) `on` f) xs

prop_nubAndDuplicatesOn :: (Integer -> Integer) -> [Integer] -> Bool
prop_nubAndDuplicatesOn f xs = nubAndDuplicatesOn f xs == (ys, xs \\ ys)
  where ys = nubBy ((==) `on` f) xs

prop_uniqOn1 :: (Integer -> Integer) -> [Integer] -> Bool
prop_uniqOn1 f xs = uniqOn f xs == sortBy (compare `on` f) (nubBy ((==) `on` f) xs)

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
tests = testProperties "Internal.Utils.List" $allProperties
