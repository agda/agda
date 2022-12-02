{-# OPTIONS_GHC -Wunused-imports #-}

-- | Utility functions for lists.

module Agda.Utils.List (module Agda.Utils.List, module X) where

-- Reexports

import Data.List as X (uncons)

-- Regular imports

import Control.Monad (filterM)

import Data.Array (Array, array, listArray)
import qualified Data.Array as Array
import Data.Bifunctor
import Data.Function (on)
import Data.Hashable
import Data.List.Split (splitOn)
import qualified Data.List as List
import qualified Data.List.NonEmpty as List1
import Data.List.NonEmpty (pattern (:|), (<|))
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap
import qualified Data.Set as Set
import Data.Strict.These

import qualified Agda.Utils.Bag as Bag
import Agda.Utils.CallStack.Base
import Agda.Utils.Function (applyWhen)
import Agda.Utils.Functor  ((<.>))
import Agda.Utils.Tuple

import {-# SOURCE #-} Agda.Utils.List1 (List1)

import Agda.Utils.Impossible

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
lastMaybe = \case
  []   -> Nothing
  x:xs -> Just $ last1 x xs

-- | Last element (safe).  Returns a default list on empty lists.
--   O(n).
lastWithDefault :: a -> [a] -> a
lastWithDefault = last1

-- | Last element of non-empty list (safe).
--   O(n).
--   @last1 a as = last (a : as)@
last1 :: a -> [a] -> a
last1 a = \case
  [] -> a
  b:bs -> last1 b bs

-- | Last two elements (safe).
--   O(n).
--
last2 :: [a] -> Maybe (a, a)
last2 (x : y : xs) = Just $ last2' x y xs
last2 _ = Nothing

-- | @last2' x y zs@ computes the last two elements of @x:y:zs@.
--   O(n).
--
last2' :: a -> a -> [a] -> (a, a)
last2' x y = \case
  []  -> (x, y)
  z:zs -> last2' y z zs

-- | Maybe cons.
--   O(1).
--   @mcons ma as = maybeToList ma ++ as@
mcons :: Maybe a -> [a] -> [a]
mcons ma as = maybe as (:as) ma

-- | 'init' and 'last' in one go, safe.
--   O(n).
initLast :: [a] -> Maybe ([a],a)
initLast []     = Nothing
initLast (a:as) = Just $ initLast1 a as

-- | 'init' and 'last' of non-empty list, safe.
--   O(n).
--   @initLast1 a as = (init (a:as), last (a:as)@
initLast1 :: a -> [a] -> ([a], a)
initLast1 a = \case
  []   -> ([], a)
  b:bs -> first (a:) $ initLast1 b bs

-- | 'init' of non-empty list, safe.
--   O(n).
--   @init1 a as = init (a:as)@
init1 :: a -> [a] -> [a]
init1 a = \case
  []   -> []
  b:bs -> a : init1 b bs

-- | @init@, safe.
--   O(n).
initMaybe :: [a] -> Maybe [a]
initMaybe = \case
  []   -> Nothing
  a:as -> Just $ init1 a as

-- | @init@, safe.
--   O(n).
initWithDefault :: [a] -> [a] -> [a]
initWithDefault as []     = as
initWithDefault _  (a:as) = init1 a as

---------------------------------------------------------------------------
-- * Lookup and indexing
---------------------------------------------------------------------------

-- | Lookup function (safe).
--   O(min n index).
(!!!) :: [a] -> Int -> Maybe a
xs !!! (!i)
  | i < 0     = Nothing
  | otherwise = index xs i
  where
  index []       !i = Nothing
  index (x : xs) 0  = Just x
  index (x : xs) i  = index xs (i - 1)

-- | A variant of 'Prelude.!!' that might provide more informative
-- error messages if the index is out of bounds.
--
-- Precondition: The index should not be out of bounds.

(!!) :: HasCallStack => [a] -> Int -> a
xs !! i = case xs !!! i of
  Just x  -> x
  Nothing -> __IMPOSSIBLE__

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
findWithIndex p as = List.find (p . fst) (zip as [0..])

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
updateHead _ []       = []
updateHead f (a : as) = f a : as

-- | Update the last element of a list, if it exists.
--   O(n).
updateLast :: (a -> a) -> [a] -> [a]
updateLast _ [] = []
updateLast f (a : as) = loop a as
  -- Using a helper function to minimize the pattern matching.
  where
  loop a []       = [f a]
  loop a (b : bs) = a : loop b bs

-- | Update nth element of a list, if it exists.
--   @O(min index n)@.
--
--   Precondition: the index is >= 0.
updateAt :: Int -> (a -> a) -> [a] -> [a]
updateAt _ _ [] = []
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

-- | Breaks a list just /after/ an element satisfying the predicate is
--   found.
--
--   >>> breakAfter1 even 1 [3,5,2,4,7,8]
--   (1 :| [3,5,2],[4,7,8])

breakAfter1 :: (a -> Bool) -> a -> [a] -> (List1 a, [a])
breakAfter1 p = loop
  where
  loop x = \case
    xs@[]         -> (x :| [], xs)
    xs@(y : ys)
      | p x       -> (x :| [], xs)
      | otherwise -> let (vs, ws) = loop y ys in (x <| vs, ws)

-- | Breaks a list just /after/ an element satisfying the predicate is
--   found.
--
--   >>> breakAfter even [1,3,5,2,4,7,8]
--   ([1,3,5,2],[4,7,8])

breakAfter :: (a -> Bool) -> [a] -> ([a], [a])
breakAfter p = \case
  []   -> ([], [])
  x:xs -> first List1.toList $ breakAfter1 p x xs

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

-- | @dropFrom marker xs@ drops everything from @xs@
-- starting with (and including) @marker@.
--
-- If the marker does not appear, the string is returned unchanged.
--
-- The following two properties hold provided @marker@ has no overlap with @xs@:
--
-- @
--   dropFrom marker (xs ++ marker ++ ys) == xs
--   dropFrom marker xs == xs
-- @
dropFrom :: Eq a => List1 a -> [a] -> [a]
dropFrom marker xs = headWithDefault __IMPOSSIBLE__ $ splitOn (List1.toList marker) xs

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

-- | Returns a list with one boolean for each non-empty suffix of the
-- list, starting with the longest suffix (the entire list). Each
-- boolean is 'True' exactly when every element in the corresponding
-- suffix satisfies the predicate.
--
-- An example:
-- @
--  'suffixesSatisfying' 'Data.Char.isLower' "AbCde" =
--  [False, False, False, True, True]
-- @
--
-- For total predicates @p@ and finite and total lists @xs@ the
-- following holds:
-- @
--  'suffixesSatisfying' p xs = 'map' ('all' p) ('List.init' ('List.tails' xs))
-- @
suffixesSatisfying :: (a -> Bool) -> [a] -> [Bool]
suffixesSatisfying p =
  snd .
  foldr (\x (b, bs) -> let !b' = p x && b in (b', b' : bs))
        (True, [])

-- ** Finding overlap

-- | Find the longest suffix of the first string @xs@
--   that is a prefix of the second string @ys@.
--   So, basically, find the overlap where the strings can be glued together.
--   Returns the index where the overlap starts and the length of the overlap.
--   The length of the overlap plus the index is the length of the first string.
--   Note that in the worst case, the empty overlap @(length xs,0)@ is returned.
--
--   Worst-case time complexity is quadratic: @O(min(n,m)²)@
--   where @n = length xs@ and @m = length ys@.
--
--   There might be asymptotically better implementations following
--   Knuth-Morris-Pratt (KMP), but for rather short lists this is good enough.
--
findOverlap :: forall a. Eq a => [a] -> [a] -> (Int, Int)
findOverlap xs ys =
  headWithDefault __IMPOSSIBLE__ $ mapMaybe maybePrefix $ zip [0..] (List.tails xs)
  where
  maybePrefix :: (Int, [a]) -> Maybe (Int, Int)
  maybePrefix (k, xs')
    | xs' `List.isPrefixOf` ys = Just (k, length xs')
    | otherwise                = Nothing

---------------------------------------------------------------------------
-- * Chunks
---------------------------------------------------------------------------

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
chopWhen :: forall a. (a -> Bool) -> [a] -> [[a]]
chopWhen p []     = []
chopWhen p (x:xs) = loop (x :| xs)
  where
  -- Local function to avoid unnecessary pattern matching.
  loop :: List1 a -> [[a]]
  loop xs = case List1.break p xs of
    (w, []        ) -> [w]
    (w, _ : []    ) -> [w, []]
    (w, _ : y : ys) -> w : loop (y :| ys)

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
sorted = allConsecutive (<=)

-- | Check whether all consecutive elements of a list satisfy the given relation.
-- O(n).
--
allConsecutive :: (a -> a -> Bool) -> [a] -> Bool
allConsecutive cmp xs = and $ zipWith cmp xs $ drop 1 xs

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
    dup (a :| _ : _) = Just a
    dup _            = Nothing

-- | Remove the first representative for each list element.
--   Thus, returns all duplicate copies.
--   O(n log n).
--
--   @allDuplicates xs == sort $ xs \\ nub xs@.
allDuplicates :: Ord a => [a] -> [a]
allDuplicates = concatMap (List1.tail . List1.reverse) . Bag.groups . Bag.fromList
  -- The reverse is necessary to actually remove the *first* occurrence
  -- of each element.

-- | Partition a list into first and later occurrences of elements
--   (modulo some quotient given by a representation function).
--
--  Time: O(n log n).
--
--  Specification:
--
--  > nubAndDuplicatesOn f xs = (ys, xs List.\\ ys)
--  >   where ys = nubOn f xs

nubAndDuplicatesOn :: Ord b => (a -> b) -> [a] -> ([a], [a])
nubAndDuplicatesOn f = loop Set.empty
  where
  loop s [] = ([], [])
  loop s (a:as)
    | b `Set.member` s = second (a:) $ loop s as
    | otherwise        = first  (a:) $ loop (Set.insert b s) as
    where b = f a

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

-- | A variant of 'nubOn' that is parametrised by a function that is
-- used to select which element from a group of equal elements that is
-- returned. The returned elements keep the order that they had in the
-- input list.
--
-- Precondition: The length of the input list must be at most
-- @'maxBound' :: 'Int'@.

nubFavouriteOn
  :: forall a b c. (Ord b, Eq c, Hashable c)
  => (a -> b)
     -- ^ The values returned by this function are used to determine
     -- which element from a group of equal elements that is returned:
     -- the smallest one is chosen (and if two elements are equally
     -- small, then the first one is chosen).
  -> (a -> c)
     -- ^ Two elements are treated as equal if this function returns
     -- the same value for both elements.
  -> [a] -> [a]
nubFavouriteOn fav f = go 0 HMap.empty
  where
  go :: Int -> HMap.HashMap c ((b, Int), a) -> [a] -> [a]
  go !pos !acc (x : xs) =
    go (1 + pos)
       (HMap.insertWith
          (\new old -> if fst new < fst old then new else old)
          (f x) ((fav x, pos), x) acc)
       xs
  go _ acc [] =
    map snd $ List.sortBy (compare `on` snd . fst) $
    HMap.elems acc

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
-- > uniqOn f == 'List.sortBy' (compare `'on'` f) . 'nubBy' ((==) `'on'` f)
--
-- If there are several elements with the same @f@-representative,
-- the first of these is kept.
--
uniqOn :: Ord b => (a -> b) -> [a] -> [a]
uniqOn key = Map.elems . Map.fromListWith (\ _ -> id) . map (\ a -> (key a, a))

-- | Checks if all the elements in the list are equal. Assumes that
--   the 'Eq' instance stands for an equivalence relation.
--   O(n).
allEqual :: Eq a => [a] -> Bool
allEqual []       = True
allEqual (x : xs) = all (== x) xs

-- | Non-efficient, monadic 'nub'.
-- O(n²).
nubM :: Monad m => (a -> a -> m Bool) -> [a] -> m [a]
nubM eq = loop where
  loop []     = return []
  loop (a:as) = (a :) <$> do loop =<< filterM (not <.> eq a) as

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

-- | Analogous to zip, combines two lists by taking the union using These (strict).
align :: [a] -> [b] -> [These a b]
align xs [] = This <$> xs
align [] ys = That <$> ys
align (x:xs) (y:ys) = These x y : align xs ys

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
    where (i', j') = (i + 1, j + 1)
  n   = length xs
  m   = length ys
  xsA, ysA :: Array Int a
  xsA = listArray (0, n - 1) xs
  ysA = listArray (0, m - 1) ys


mergeStrictlyOrderedBy :: (a -> a -> Bool) -> [a] -> [a] -> Maybe [a]
mergeStrictlyOrderedBy (<) = loop where
  loop [] ys = Just ys
  loop xs [] = Just xs
  loop (x:xs) (y:ys)
    | x < y = (x:) <$> loop xs (y:ys)
    | y < x = (y:) <$> loop (x:xs) ys
    | otherwise = Nothing
