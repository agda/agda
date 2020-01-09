-- | Utility functions for lists.

module Agda.Utils.List where

import Control.Arrow (first, second)

import Data.Array (Array, array, listArray)
import qualified Data.Array as Array
import Data.Functor ((<$>))
import Data.Function
import qualified Data.List as List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Agda.Utils.Bag as Bag
import Agda.Utils.Function (applyWhen)
import Agda.Utils.Tuple

---------------------------------------------------------------------------
-- * Variants of list case, cons, head, tail, init, last
---------------------------------------------------------------------------

-- | Append a single element at the end.
--   Time: O(length); use only on small lists.
snoc :: [a] -> a -> [a]
snoc xs x = xs ++ [x]

-- | Case distinction for lists, with list first.
--   O(1).
--
--   Cf. 'Agda.Utils.Null.ifNull'.
caseList :: [a] -> b -> (a -> [a] -> b) -> b
caseList xs n c = listCase n c xs

-- | Case distinction for lists, with list first.
--   O(1).
--
--   Cf. 'Agda.Utils.Null.ifNull'.
caseListM :: Monad m => m [a] -> m b -> (a -> [a] -> m b) -> m b
caseListM mxs n c = listCase n c =<< mxs

-- | Case distinction for lists, with list last.
--   O(1).
--
listCase :: b -> (a -> [a] -> b) -> [a] -> b
listCase n c []     = n
listCase n c (x:xs) = c x xs

-- | Head function (safe). Returns a default value on empty lists.
--   O(1).
--
-- > headWithDefault 42 []      = 42
-- > headWithDefault 42 [1,2,3] = 1
headWithDefault :: a -> [a] -> a
headWithDefault def = fromMaybe def . listToMaybe

-- | Tail function (safe).
--   O(1).
tailMaybe :: [a] -> Maybe [a]
tailMaybe = fmap snd . uncons

-- | Tail function (safe).  Returns a default list on empty lists.
--   O(1).
tailWithDefault :: [a] -> [a] -> [a]
tailWithDefault def = fromMaybe def . tailMaybe

-- | Last element (safe).
--   O(n).
lastMaybe :: [a] -> Maybe a
lastMaybe [] = Nothing
lastMaybe xs = Just $ last xs

-- | Last two elements (safe).
--   O(n).
last2 :: [a] -> Maybe (a, a)
last2 (x : y : xs) = Just $ loop x y xs
  where
  loop x y []     = (x, y)
  loop x y (z:xs) = loop y z xs
last2 _ = Nothing

-- | Opposite of cons @(:)@, safe.
--   O(1).
uncons :: [a] -> Maybe (a, [a])
uncons []     = Nothing
uncons (x:xs) = Just (x,xs)

-- | Maybe cons.
--   O(1).
--   @mcons ma as = maybeToList ma ++ as@
mcons :: Maybe a -> [a] -> [a]
mcons ma as = maybe as (:as) ma

-- | 'init' and 'last' in one go, safe.
--   O(n).
initLast :: [a] -> Maybe ([a],a)
initLast []     = Nothing
initLast (a:as) = Just $ loop a as where
  loop a []      = ([], a)
  loop a (b : bs) = mapFst (a:) $ loop b bs

-- | @init@, safe.
--   O(n).
initMaybe :: [a] -> Maybe [a]
initMaybe = fmap fst . initLast

---------------------------------------------------------------------------
-- * Lookup and indexing
---------------------------------------------------------------------------

-- | Lookup function (partially safe).
--   O(min n index).
(!!!) :: [a] -> Int -> Maybe a
[]       !!! _         = Nothing
(x : _)  !!! 0         = Just x
(_ : xs) !!! n         = xs !!! (n - 1)

-- | Lookup function with default value for index out of range.
--   O(min n index).
--
--   The name is chosen akin to 'Data.List.genericIndex'.
indexWithDefault :: a -> [a] -> Int -> a
indexWithDefault a []       _ = a
indexWithDefault a (x : _)  0 = x
indexWithDefault a (_ : xs) n = indexWithDefault a xs (n - 1)

-- | Find an element satisfying a predicate and return it with its index.
--   O(n) in the worst case, e.g. @findWithIndex f xs = Nothing@.
--
--   TODO: more efficient implementation!?
findWithIndex :: (a -> Bool) -> [a] -> Maybe (a, Int)
findWithIndex p as = listToMaybe $ filter (p . fst) $ zip as [0..]

-- | A generalised variant of 'elemIndex'.
-- O(n).
genericElemIndex :: (Eq a, Integral i) => a -> [a] -> Maybe i
genericElemIndex x xs =
  listToMaybe $
  map fst $
  filter snd $
  zip [0..] $
  map (== x) xs

-- | @downFrom n = [n-1,..1,0]@.
--   O(n).
downFrom :: Integral a => a -> [a]
downFrom n | n <= 0     = []
           | otherwise = let n' = n-1 in n' : downFrom n'

---------------------------------------------------------------------------
-- * Update
---------------------------------------------------------------------------

-- | Update the first element of a list, if it exists.
--   O(1).
updateHead :: (a -> a) -> [a] -> [a]
updateHead f [] = []
updateHead f (a : as) = f a : as

-- | Update the last element of a list, if it exists.
--   O(n).
updateLast :: (a -> a) -> [a] -> [a]
updateLast f [] = []
updateLast f [a] = [f a]
updateLast f (a : as@(_ : _)) = a : updateLast f as

-- | Update nth element of a list, if it exists.
--   @O(min index n)@.
--
--   Precondition: the index is >= 0.
updateAt :: Int -> (a -> a) -> [a] -> [a]
updateAt _ f [] = []
updateAt 0 f (a : as) = f a : as
updateAt n f (a : as) = a : updateAt (n-1) f as

---------------------------------------------------------------------------
-- * Sublist extraction and partitioning
---------------------------------------------------------------------------

type Prefix a = [a]  -- ^ The list before the split point.
type Suffix a = [a]  -- ^ The list after the split point.

-- | @splitExactlyAt n xs = Just (ys, zs)@ iff @xs = ys ++ zs@
--   and @genericLength ys = n@.
splitExactlyAt :: Integral n => n -> [a] -> Maybe (Prefix a, Suffix a)
splitExactlyAt 0 xs       = return ([], xs)
splitExactlyAt n []       = Nothing
splitExactlyAt n (x : xs) = mapFst (x :) <$> splitExactlyAt (n-1) xs

-- | Drop from the end of a list.
--   O(length).
--
--   @dropEnd n = reverse . drop n . reverse@
--
--   Forces the whole list even for @n==0@.
dropEnd :: forall a. Int -> [a] -> Prefix a
dropEnd n = snd . foldr f (n, [])
  where
  f :: a -> (Int, [a]) -> (Int, [a])
  f x (n, xs) = (n-1, applyWhen (n <= 0) (x:) xs)

-- | Split off the largest suffix whose elements satisfy a predicate.
--   O(n).
--
--   @spanEnd p xs = (ys, zs)@
--   where @xs = ys ++ zs@
--   and @all p zs@
--   and @maybe True (not . p) (lastMaybe yz)@.
spanEnd :: forall a. (a -> Bool) -> [a] -> (Prefix a, Suffix a)
spanEnd p = snd . foldr f (True, ([], []))
  where
  f :: a -> (Bool, ([a], [a])) -> (Bool, ([a], [a]))
  f x (b', (xs, ys)) = (b, if b then (xs, x:ys) else (x:xs, ys))
    where b = b' && p x

-- | A generalized version of @takeWhile@.
--   (Cf. @mapMaybe@ vs. @filter@).
--   @O(length . takeWhileJust f).
--
--   @takeWhileJust f = fst . spanJust f@.
takeWhileJust :: (a -> Maybe b) -> [a] -> Prefix b
takeWhileJust p = loop
  where
    loop (a : as) | Just b <- p a = b : loop as
    loop _ = []

-- | A generalized version of @span@.
--   @O(length . fst . spanJust f)@.
spanJust :: (a -> Maybe b) -> [a] -> (Prefix b, Suffix a)
spanJust p = loop
  where
    loop (a : as) | Just b <- p a = mapFst (b :) $ loop as
    loop as                       = ([], as)

-- | Partition a list into 'Nothing's and 'Just's.
--   O(n).
--
--   @partitionMaybe f = partitionEithers . map (\ a -> maybe (Left a) Right (f a))@
--
--   Note: @'mapMaybe' f = snd . partitionMaybe f@.
partitionMaybe :: (a -> Maybe b) -> [a] -> ([a], [b])
partitionMaybe f = loop
  where
    loop []       = ([], [])
    loop (a : as) = case f a of
      Nothing -> mapFst (a :) $ loop as
      Just b  -> mapSnd (b :) $ loop as

-- | Like 'filter', but additionally return the last partition
--   of the list where the predicate is @False@ everywhere.
--   O(n).
filterAndRest :: (a -> Bool) -> [a] -> ([a], Suffix a)
filterAndRest p = mapMaybeAndRest $ \ a -> if p a then Just a else Nothing

-- | Like 'mapMaybe', but additionally return the last partition
--   of the list where the function always returns @Nothing@.
--   O(n).
mapMaybeAndRest :: (a -> Maybe b) -> [a] -> ([b], Suffix a)
mapMaybeAndRest f = loop [] where
  loop acc = \case
    []                   -> ([], reverse acc)
    x:xs | Just y <- f x -> first (y:) $ loop [] xs
         | otherwise     -> loop (x:acc) xs

-- | Sublist relation.
isSublistOf :: Eq a => [a] -> [a] -> Bool
isSublistOf = List.isSubsequenceOf

-- | All ways of removing one element from a list.
--   O(n²).
holes :: [a] -> [(a, [a])]
holes []     = []
holes (x:xs) = (x, xs) : map (second (x:)) (holes xs)

---------------------------------------------------------------------------
-- * Prefix and suffix
---------------------------------------------------------------------------

-- ** Prefix

-- | Compute the common prefix of two lists.
--   O(min n m).
commonPrefix :: Eq a => [a] -> [a] -> Prefix a
commonPrefix [] _ = []
commonPrefix _ [] = []
commonPrefix (x:xs) (y:ys)
  | x == y    = x : commonPrefix xs ys
  | otherwise = []

-- | Drops from both lists simultaneously until one list is empty.
--   O(min n m).
dropCommon :: [a] -> [b] -> (Suffix a, Suffix b)
dropCommon (x : xs) (y : ys) = dropCommon xs ys
dropCommon xs ys = (xs, ys)

-- | Check if a list has a given prefix. If so, return the list
--   minus the prefix.
--   O(length prefix).
stripPrefixBy :: (a -> a -> Bool) -> Prefix a -> [a] -> Maybe (Suffix a)
stripPrefixBy eq = loop
  where
  loop []    rest = Just rest
  loop (_:_) []   = Nothing
  loop (p:pat) (r:rest)
    | eq p r    = loop pat rest
    | otherwise = Nothing

-- ** Suffix

-- | Compute the common suffix of two lists.
--   O(n + m).
commonSuffix :: Eq a => [a] -> [a] -> Suffix a
commonSuffix xs ys = reverse $ (commonPrefix `on` reverse) xs ys

-- | @stripSuffix suf xs = Just pre@ iff @xs = pre ++ suf@.
-- O(n).
stripSuffix :: Eq a => Suffix a -> [a] -> Maybe (Prefix a)
stripSuffix [] = Just
stripSuffix s  = stripReversedSuffix (reverse s)

type ReversedSuffix a = [a]

-- | @stripReversedSuffix rsuf xs = Just pre@ iff @xs = pre ++ reverse suf@.
--   O(n).
stripReversedSuffix :: forall a. Eq a => ReversedSuffix a -> [a] -> Maybe (Prefix a)
stripReversedSuffix rs = final . foldr step (SSSStrip rs)
  where
  -- Step of the automaton (reading input from right to left).
  step :: a -> StrSufSt a -> StrSufSt a
  step x = \case
    SSSMismatch   -> SSSMismatch
    SSSResult xs  -> SSSResult (x:xs)
    SSSStrip []   -> SSSResult [x]
    SSSStrip (y:ys)
      | x == y    -> SSSStrip ys
      | otherwise -> SSSMismatch

  -- Output of the automaton.
  final :: StrSufSt a -> Maybe (Prefix a)
  final = \case
    SSSResult xs -> Just xs
    SSSStrip []  -> Just []
    _            -> Nothing  -- We have not stripped the whole suffix or encountered a mismatch.

-- | Internal state for stripping suffix.
data StrSufSt a
  = SSSMismatch                 -- ^ Error.
  | SSSStrip (ReversedSuffix a) -- ^ "Negative string" to remove from end. List may be empty.
  | SSSResult [a]               -- ^ "Positive string" (result). Non-empty list.

---------------------------------------------------------------------------
-- * Groups and chunks
---------------------------------------------------------------------------

-- | @'groupOn' f = 'groupBy' (('==') \`on\` f) '.' 'List.sortBy' ('compare' \`on\` f)@.
-- O(n log n).
groupOn :: Ord b => (a -> b) -> [a] -> [[a]]
groupOn f = List.groupBy ((==) `on` f) . List.sortBy (compare `on` f)

-- | A variant of 'List.groupBy' which applies the predicate to consecutive
-- pairs.
-- O(n).
groupBy' :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy' _ []           = []
groupBy' p xxs@(x : xs) = grp x $ zipWith (\x y -> (p x y, y)) xxs xs
  where
  grp x ys = (x : map snd xs) : tail
    where (xs, rest) = span fst ys
          tail = case rest of
                   []            -> []
                   ((_, z) : zs) -> grp z zs

-- | Split a list into sublists. Generalisation of the prelude function
--   @words@.
--   O(n).
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
-- O(n).
chop :: Int -> [a] -> [[a]]
chop _ [] = []
chop n xs = ys : chop n zs
    where (ys,zs) = splitAt n xs

-- | Chop a list at the positions when the predicate holds. Contrary to
--   'wordsBy', consecutive separator elements will result in an empty segment
--   in the result.
--   O(n).
--
--    > intercalate [x] (chopWhen (== x) xs) == xs
chopWhen :: (a -> Bool) -> [a] -> [[a]]
chopWhen p [] = []
chopWhen p xs =
  case break p xs of
    (w, [])     -> [w]
    (w, [_])    -> [w, []]
    (w, _ : ys) -> w : chopWhen p ys

---------------------------------------------------------------------------
-- * List as sets
---------------------------------------------------------------------------

-- | Check membership for the same list often.
--   Use partially applied to create membership predicate
--   @hasElem xs :: a -> Bool@.
--
--   * First time: @O(n log n)@ in the worst case.
--   * Subsequently: @O(log n)@.
--
--   Specification: @hasElem xs == (`elem` xs)@.
hasElem :: Ord a => [a] -> a -> Bool
hasElem xs = (`Set.member` Set.fromList xs)

-- | Check whether a list is sorted.
-- O(n).
--
-- Assumes that the 'Ord' instance implements a partial order.

sorted :: Ord a => [a] -> Bool
sorted [] = True
sorted xs = and $ zipWith (<=) xs (tail xs)

-- | Check whether all elements in a list are distinct from each other.
--   Assumes that the 'Eq' instance stands for an equivalence relation.
--
--   O(n²) in the worst case @distinct xs == True@.
distinct :: Eq a => [a] -> Bool
distinct []     = True
distinct (x:xs) = x `notElem` xs && distinct xs

-- | An optimised version of 'distinct'.
--   O(n log n).
--
--   Precondition: The list's length must fit in an 'Int'.

fastDistinct :: Ord a => [a] -> Bool
fastDistinct xs = Set.size (Set.fromList xs) == length xs

-- | Returns an (arbitrary) representative for each list element
--   that occurs more than once.
--   O(n log n).
duplicates :: Ord a => [a] -> [a]
duplicates = mapMaybe dup . Bag.groups . Bag.fromList
  where
    dup (a : _ : _) = Just a
    dup _           = Nothing

-- | Remove the first representative for each list element.
--   Thus, returns all duplicate copies.
--   O(n log n).
--
--   @allDuplicates xs == sort $ xs \\ nub xs@.
allDuplicates :: Ord a => [a] -> [a]
allDuplicates = concat . map (drop 1 . reverse) . Bag.groups . Bag.fromList
  -- The reverse is necessary to actually remove the *first* occurrence
  -- of each element.

-- | Efficient variant of 'nubBy' for lists, using a set to store already seen elements.
-- O(n log n)
--
-- Specification:
--
-- > nubOn f xs == 'nubBy' ((==) `'on'` f) xs.

nubOn :: Ord b => (a -> b) -> [a] -> [a]
nubOn f = loop Set.empty
  where
  loop s [] = []
  loop s (a:as)
    | b `Set.member` s = loop s as
    | otherwise        = a : loop (Set.insert b s) as
    where b = f a

-- Andreas, 2019-11-16
-- The implementation of nubOn using Set can be more than 1000-times
-- faster than the following old one using List.sort.
-- (Tested using criterion and -O on some lists of length 100.000.)

-- -- | Efficient variant of 'nubBy' for finite lists (using sorting).
-- -- O(n log n)
-- --
-- -- Specification:
-- --
-- -- > nubOn2 f xs == 'nubBy' ((==) `'on'` f) xs.
--
-- nubOn2 :: Ord b => (a -> b) -> [a] -> [a]
-- nubOn2 tag =
--     -- Throw away numbering
--   map snd
--     -- Restore original order
--   . List.sortBy (compare `on` fst)
--     -- Retain first entry of each @tag@ group
--   . map (snd . head)
--   . List.groupBy ((==) `on` fst)
--     -- Sort by tag (stable)
--   . List.sortBy (compare `on` fst)
--     -- Tag with @tag@ and sequential numbering
--   . map (\p@(_, x) -> (tag x, p))
--   . zip [1..]

-- | Efficient variant of 'nubBy' for finite lists.
-- O(n log n).
--
-- Specification: For each list @xs@ there is a list @ys@ which is a
-- permutation of @xs@ such that
--
-- > uniqOn f xs == 'nubBy' ((==) `'on'` f) ys.
--
-- Furthermore:
--
-- > List.sortBy (compare `on` f) (uniqOn f xs) == uniqOn f xs
-- > uniqOn id == Set.toAscList . Set.fromList
--
uniqOn :: Ord b => (a -> b) -> [a] -> [a]
uniqOn key = Map.elems . Map.fromList . map (\ a -> (key a, a))

-- | Checks if all the elements in the list are equal. Assumes that
--   the 'Eq' instance stands for an equivalence relation.
--   O(n).
allEqual :: Eq a => [a] -> Bool
allEqual []       = True
allEqual (x : xs) = all (== x) xs

---------------------------------------------------------------------------
-- * Zipping
---------------------------------------------------------------------------

-- | Requires both lists to have the same length.
--   O(n).
--
--   Otherwise, @Nothing@ is returned.

zipWith' :: (a -> b -> c) -> [a] -> [b] -> Maybe [c]
zipWith' f = loop
  where
  loop []        []      = Just []
  loop (x : xs) (y : ys) = (f x y :) <$> loop xs ys
  loop []       (_ : _)  = Nothing
  loop (_ : _)  []       = Nothing

-- | Like 'zipWith' but keep the rest of the second list as-is
--   (in case the second list is longer).
-- O(n).
--
-- @
--   zipWithKeepRest f as bs == zipWith f as bs ++ drop (length as) bs
-- @
zipWithKeepRest :: (a -> b -> b) -> [a] -> [b] -> [b]
zipWithKeepRest f = loop
  where
  loop []       bs       = bs
  loop as       []       = []
  loop (a : as) (b : bs) = f a b : loop as bs

-- -- UNUSED; a better type would be
-- -- zipWithTails :: (a -> b -> c) -> [a] -> [b] -> ([c], Either [a] [b])

-- -- | Like zipWith, but returns the leftover elements of the input lists.
-- zipWithTails :: (a -> b -> c) -> [a] -> [b] -> ([c], [a] , [b])
-- zipWithTails f xs       []       = ([], xs, [])
-- zipWithTails f []       ys       = ([], [] , ys)
-- zipWithTails f (x : xs) (y : ys) = (f x y : zs , as , bs)
--   where (zs , as , bs) = zipWithTails f xs ys


---------------------------------------------------------------------------
-- * Unzipping
---------------------------------------------------------------------------

unzipWith :: (a -> (b, c)) -> [a] -> ([b], [c])
unzipWith f = unzip . map f

---------------------------------------------------------------------------
-- * Edit distance
---------------------------------------------------------------------------

-- | Implemented using tree recursion, don't run me at home!
--   O(3^(min n m)).
editDistanceSpec :: Eq a => [a] -> [a] -> Int
editDistanceSpec [] ys = length ys
editDistanceSpec xs [] = length xs
editDistanceSpec (x : xs) (y : ys)
  | x == y    = editDistanceSpec xs ys
  | otherwise = 1 + minimum [ editDistanceSpec (x : xs) ys
                            , editDistanceSpec xs (y : ys)
                            , editDistanceSpec xs ys ]

-- | Implemented using dynamic programming and @Data.Array@.
--   O(n*m).
editDistance :: forall a. Eq a => [a] -> [a] -> Int
editDistance xs ys = editD 0 0
  where
  editD i j = tbl Array.! (i, j)
  -- Tabulate editD' in immutable boxed array (content computed lazily).
  tbl :: Array (Int,Int) Int
  tbl = array ((0,0), (n,m)) [ ((i, j), editD' i j) | i <- [0..n], j <- [0..m] ]
  editD' i j =
    case (compare i n, compare j m) of
      -- Interior
      (LT, LT)
        | xsA Array.! i == ysA Array.! j
                    -> editD i' j'
        | otherwise -> 1 + minimum [ editD i' j, editD i j', editD i' j' ]
      -- Border: one list is empty
      (EQ, LT)      ->  m - j
      (LT, EQ)      ->  n - i
      -- Corner (EQ, EQ): both lists are empty
      _             -> 0
      -- GT cases are impossible.
    where (i',j') = (i+1, j+1)
  n   = length xs
  m   = length ys
  xsA, ysA :: Array Int a
  xsA = listArray (0,n-1) xs
  ysA = listArray (0,m-1) ys
