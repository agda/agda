{-# LANGUAGE CPP             #-}
{-# LANGUAGE PatternGuards   #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
#endif

{-| Utitlity functions on lists.
-}
module Agda.Utils.List where

import Data.Functor ((<$>))
import Data.Function
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import Text.Show.Functions ()
import Test.QuickCheck

import qualified Agda.Utils.Bag as Bag
import Agda.Utils.TestHelpers
-- import Agda.Utils.QuickCheck -- Andreas, 2014-04-27 Inconvenient
-- because cabal-only CPP directive
import Agda.Utils.Tuple

#include "undefined.h"
import Agda.Utils.Impossible

-- | Case distinction for lists, with list first.
--   Cf. 'Agda.Utils.Null.ifNull'.
caseList :: [a] -> b -> (a -> [a] -> b) -> b
caseList []     n c = n
caseList (x:xs) n c = c x xs

-- | Case distinction for lists, with list last.
listCase :: b -> (a -> [a] -> b) -> [a] -> b
listCase n c []     = n
listCase n c (x:xs) = c x xs

-- | Head function (safe).
headMaybe :: [a] -> Maybe a
headMaybe = listToMaybe

-- | Head function (safe). Returns a value on empty lists.
--
-- > headWithDefault 42 []      = 42
-- > headWithDefault 42 [1,2,3] = 1
headWithDefault :: a -> [a] -> a
headWithDefault def = fromMaybe def . headMaybe

-- | Last element (safe).
lastMaybe :: [a] -> Maybe a
lastMaybe [] = Nothing
lastMaybe xs = Just $ last xs

-- | Opposite of cons @(:)@, safe.
uncons :: [a] -> Maybe (a, [a])
uncons []     = Nothing
uncons (x:xs) = Just (x,xs)

-- | Maybe cons.   @mcons ma as = maybeToList ma ++ as@
mcons :: Maybe a -> [a] -> [a]
mcons ma as = maybe as (:as) ma

-- | 'init' and 'last' in one go, safe.
initLast :: [a] -> Maybe ([a],a)
initLast [] = Nothing
initLast as = Just $ loop as where
  loop []       = __IMPOSSIBLE__
  loop [a]      = ([], a)
  loop (a : as) = mapFst (a:) $ loop as

-- | Lookup function (partially safe).
(!!!) :: [a] -> Int -> Maybe a
_        !!! n | n < 0 = __IMPOSSIBLE__
[]       !!! _         = Nothing
(x : _)  !!! 0         = Just x
(_ : xs) !!! n         = xs !!! (n - 1)

-- | downFrom n = [n-1,..1,0]
downFrom :: Integral a => a -> [a]
downFrom n | n <= 0     = []
           | otherwise = let n' = n-1 in n' : downFrom n'

-- | Update the first element of a list, if it exists.
updateHead :: (a -> a) -> [a] -> [a]
updateHead f [] = []
updateHead f (a : as) = f a : as

spec_updateHead f as = let (bs, cs) = splitAt 1 as in map f bs ++ cs
prop_updateHead f as = updateHead f as == spec_updateHead f as

-- | Update the last element of a list, if it exists.
updateLast :: (a -> a) -> [a] -> [a]
updateLast f [] = []
updateLast f [a] = [f a]
updateLast f (a : as@(_ : _)) = a : updateLast f as

spec_updateLast f as = let (bs, cs) = splitAt (length as - 1) as in bs ++ map f cs
prop_updateLast f as = updateLast f as == spec_updateLast f as

-- | Update nth element of a list, if it exists.
--   Precondition: the index is >= 0.
updateAt :: Int -> (a -> a) -> [a] -> [a]
updateAt _ f [] = []
updateAt 0 f (a : as) = f a : as
updateAt n f (a : as) = a : updateAt (n-1) f as

spec_updateAt n f as = let (bs, cs) = splitAt n as in bs ++ updateHead f cs
prop_updateAt (NonNegative n) f as = updateAt n f as == spec_updateAt n f as

-- | A generalized version of @partition@.
--   (Cf. @mapMaybe@ vs. @filter@).
mapEither :: (a -> Either b c) -> [a] -> ([b],[c])
{-# INLINE mapEither #-}
mapEither f xs = foldr (deal f) ([],[]) xs

deal :: (a -> Either b c) -> a -> ([b],[c]) -> ([b],[c])
deal f a ~(bs,cs) = case f a of
  Left  b -> (b:bs, cs)
  Right c -> (bs, c:cs)

-- | A generalized version of @takeWhile@.
--   (Cf. @mapMaybe@ vs. @filter@).
takeWhileJust :: (a -> Maybe b) -> [a] -> [b]
takeWhileJust p = loop
  where
    loop (a : as) | Just b <- p a = b : loop as
    loop _ = []

-- | A generalized version of @span@.
spanJust :: (a -> Maybe b) -> [a] -> ([b], [a])
spanJust p = loop
  where
    loop (a : as) | Just b <- p a = mapFst (b :) $ loop as
    loop as                       = ([], as)

-- | Partition a list into 'Nothing's and 'Just's.
--   @'mapMaybe' f = snd . partitionMaybe f@.
partitionMaybe :: (a -> Maybe b) -> [a] -> ([a], [b])
partitionMaybe f = loop
  where
    loop []       = ([], [])
    loop (a : as) = case f a of
      Nothing -> mapFst (a :) $ loop as
      Just b  -> mapSnd (b :) $ loop as

-- | Sublist relation.
isSublistOf :: Eq a => [a] -> [a] -> Bool
isSublistOf []       ys = True
isSublistOf (x : xs) ys =
  case dropWhile (x /=) ys of
    []     -> False
    (_:ys) -> isSublistOf xs ys

type Prefix a = [a]
type Suffix a = [a]

-- | Check if a list has a given prefix. If so, return the list
--   minus the prefix.
maybePrefixMatch :: Eq a => Prefix a -> [a] -> Maybe (Suffix a)
maybePrefixMatch []    rest = Just rest
maybePrefixMatch (_:_) []   = Nothing
maybePrefixMatch (p:pat) (r:rest)
  | p == r    = maybePrefixMatch pat rest
  | otherwise = Nothing

-- | Result of 'preOrSuffix'.
data PreOrSuffix a
  = IsPrefix a [a] -- ^ First list is prefix of second.
  | IsSuffix a [a] -- ^ First list is suffix of second.
  | IsBothfix      -- ^ The lists are equal.
  | IsNofix        -- ^ The lists are incomparable.

-- | Compare lists with respect to prefix partial order.
preOrSuffix :: Eq a => [a] -> [a] -> PreOrSuffix a
preOrSuffix []     []     = IsBothfix
preOrSuffix []     (b:bs) = IsPrefix b bs
preOrSuffix (a:as) []     = IsSuffix a as
preOrSuffix (a:as) (b:bs)
  | a == b    = preOrSuffix as bs
  | otherwise = IsNofix

-- | Split a list into sublists. Generalisation of the prelude function
--   @words@.
--
--   > words xs == wordsBy isSpace xs
wordsBy :: (a -> Bool) -> [a] -> [[a]]
wordsBy p xs = yesP xs
    where
        yesP xs = noP (dropWhile p xs)

        noP []  = []
        noP xs  = ys : yesP zs
            where
                (ys,zs) = break p xs

-- | Chop up a list in chunks of a given length.
chop :: Int -> [a] -> [[a]]
chop _ [] = []
chop n xs = ys : chop n zs
    where (ys,zs) = splitAt n xs

-- | Chop a list at the positions when the predicate holds. Contrary to
--   'wordsBy', consecutive separator elements will result in an empty segment
--   in the result.
--    > intercalate [x] (chopWhen (== x) xs) == xs
chopWhen :: (a -> Bool) -> [a] -> [[a]]
chopWhen p [] = []
chopWhen p xs =
  case break p xs of
    (w, [])     -> [w]
    (w, [_])    -> [w, []]
    (w, _ : ys) -> w : chopWhen p ys

prop_chop_intercalate :: Property
prop_chop_intercalate =
  forAllShrink (choose (0, 4 :: Int))          shrink $ \ d ->
  forAllShrink (listOf (choose (0, 4 :: Int))) shrink $ \ xs ->
  xs === intercalate [d] (chopWhen (== d) xs)

-- | All ways of removing one element from a list.
holes :: [a] -> [(a, [a])]
holes []     = []
holes (x:xs) = (x, xs) : map (id -*- (x:)) (holes xs)

-- | Check whether a list is sorted.
--
-- Assumes that the 'Ord' instance implements a partial order.

sorted :: Ord a => [a] -> Bool
sorted [] = True
sorted xs = and $ zipWith (<=) xs (tail xs)

-- | Check whether all elements in a list are distinct from each
-- other. Assumes that the 'Eq' instance stands for an equivalence
-- relation.
distinct :: Eq a => [a] -> Bool
distinct []     = True
distinct (x:xs) = x `notElem` xs && distinct xs

-- | An optimised version of 'distinct'.
--
-- Precondition: The list's length must fit in an 'Int'.

fastDistinct :: Ord a => [a] -> Bool
fastDistinct xs = Set.size (Set.fromList xs) == length xs

prop_distinct_fastDistinct :: [Integer] -> Bool
prop_distinct_fastDistinct xs = distinct xs == fastDistinct xs

-- | Checks if all the elements in the list are equal. Assumes that
-- the 'Eq' instance stands for an equivalence relation.
allEqual :: Eq a => [a] -> Bool
allEqual []       = True
allEqual (x : xs) = all (== x) xs

-- | Returns an (arbitrary) representative for each list element
--   that occurs more than once.
duplicates :: Ord a => [a] -> [a]
duplicates = mapMaybe dup . Bag.groups . Bag.fromList
  where
    dup (a : _ : _) = Just a
    dup _           = Nothing

-- | A variant of 'groupBy' which applies the predicate to consecutive
-- pairs.

groupBy' :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy' _ []           = []
groupBy' p xxs@(x : xs) = grp x $ zipWith (\x y -> (p x y, y)) xxs xs
  where
  grp x ys = (x : map snd xs) : tail
    where (xs, rest) = span fst ys
          tail = case rest of
                   []            -> []
                   ((_, z) : zs) -> grp z zs

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

-- | @'groupOn' f = 'groupBy' (('==') \`on\` f) '.' 'sortBy' ('compare' \`on\` f)@.

groupOn :: Ord b => (a -> b) -> [a] -> [[a]]
groupOn f = groupBy ((==) `on` f) . sortBy (compare `on` f)

-- | @splitExactlyAt n xs = Just (ys, zs)@ iff @xs = ys ++ zs@
--   and @genericLength ys = n@.
splitExactlyAt :: Integral n => n -> [a] -> Maybe ([a], [a])
splitExactlyAt 0 xs       = return ([], xs)
splitExactlyAt n []       = Nothing
splitExactlyAt n (x : xs) = mapFst (x :) <$> splitExactlyAt (n-1) xs

-- | @'extractNthElement' n xs@ gives the @n@-th element in @xs@
-- (counting from 0), plus the remaining elements (preserving order).

extractNthElement' :: Integral i => i -> [a] -> ([a], a, [a])
extractNthElement' n xs = (left, el, right)
  where
  (left, el : right) = genericSplitAt n xs

extractNthElement :: Integral i => i -> [a] -> (a, [a])
extractNthElement n xs = (el, left ++ right)
  where
  (left, el, right) = extractNthElement' n xs

prop_extractNthElement :: Integer -> [Integer] -> Property
prop_extractNthElement n xs =
  0 <= n && n < genericLength xs ==>
    genericTake n rest ++ [elem] ++ genericDrop n rest == xs
  where (elem, rest) = extractNthElement n xs

-- | A generalised variant of 'elemIndex'.

genericElemIndex :: (Eq a, Integral i) => a -> [a] -> Maybe i
genericElemIndex x xs =
  listToMaybe $
  map fst $
  filter snd $
  zip [0..] $
  map (== x) xs

prop_genericElemIndex :: Integer -> [Integer] -> Property
prop_genericElemIndex x xs =
  classify (x `elem` xs) "members" $
    genericElemIndex x xs == elemIndex x xs

-- | Requires both lists to have the same length.

zipWith' :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith' f []        []      = []
zipWith' f (x : xs) (y : ys) = f x y : zipWith' f xs ys
zipWith' f []       (_ : _)  = {- ' -} __IMPOSSIBLE__
zipWith' f (_ : _)  []       = {- ' -} __IMPOSSIBLE__

prop_zipWith' :: (Integer -> Integer -> Integer) -> Property
prop_zipWith' f =
  forAll natural $ \n ->
    forAll (two $ vector n) $ \(xs, ys) ->
      zipWith' f xs ys == zipWith f xs ys

{- UNUSED; a better type would be
   zipWithTails :: (a -> b -> c) -> [a] -> [b] -> ([c], Either [a] [b])

-- | Like zipWith, but returns the leftover elements of the input lists.
zipWithTails :: (a -> b -> c) -> [a] -> [b] -> ([c], [a] , [b])
zipWithTails f xs       []       = ([], xs, [])
zipWithTails f []       ys       = ([], [] , ys)
zipWithTails f (x : xs) (y : ys) = (f x y : zs , as , bs)
  where (zs , as , bs) = zipWithTails f xs ys
-}

-- | Efficient variant of 'nubBy' for finite lists.
--
-- Specification:
--
-- > nubOn f xs == 'nubBy' ((==) `'on'` f) xs.
nubOn :: Ord b => (a -> b) -> [a] -> [a]
nubOn tag =
  map snd
  . sortBy (compare `on` fst)
  . map (snd . head)
  . groupBy ((==) `on` fst)
  . sortBy (compare `on` fst)
  . map (\p@(_, x) -> (tag x, p))
  . zip [1..]

prop_nubOn :: (Integer -> Integer) -> [Integer] -> Bool
prop_nubOn f xs = nubOn f xs == nubBy ((==) `on` f) xs

-- | Efficient variant of 'nubBy' for finite lists.
--
-- Specification: For each list @xs@ there is a list @ys@ which is a
-- permutation of @xs@ such that
--
-- > uniqOn f xs == 'nubBy' ((==) `'on'` f) ys.
--
-- Furthermore
--
-- > sortBy (compare `on` f) (uniqOn f xs) == uniqOn f xs.
uniqOn :: Ord b => (a -> b) -> [a] -> [a]
uniqOn key = Map.elems . Map.fromList . map (\ a -> (key a, a))

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

-- | Compute the common suffix of two lists.
commonSuffix :: Eq a => [a] -> [a] -> [a]
commonSuffix xs ys = reverse $ (commonPrefix `on` reverse) xs ys

-- | Compute the common prefix of two lists.
commonPrefix :: Eq a => [a] -> [a] -> [a]
commonPrefix [] _ = []
commonPrefix _ [] = []
commonPrefix (x:xs) (y:ys)
  | x == y    = x : commonPrefix xs ys
  | otherwise = []

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

-- Hack to make $quickCheckAll work under ghc-7.8
return []

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = do
  putStrLn "Agda.Utils.List"
  $quickCheckAll

-- tests = runTests "Agda.Utils.List"
--   [ quickCheck' prop_distinct_fastDistinct
--   , quickCheck' prop_groupBy'
--   , quickCheck' prop_extractNthElement
--   , quickCheck' prop_genericElemIndex
--   , quickCheck' prop_zipWith'
--   , quickCheck' prop_uniqOn
--   ]
