
-- | Utility functions for lists.

module Agda.Utils.List where

import Control.Arrow (first)

import Data.Functor ((<$>))
import Data.Function
import qualified Data.List as List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import Text.Show.Functions ()

import qualified Agda.Utils.Bag as Bag

import Agda.Utils.Tuple

-- | Append a single element at the end.
--   Time: O(length); use only on small lists.
snoc :: [a] -> a -> [a]
snoc xs x = xs ++ [x]

-- | Case distinction for lists, with list first.
--   Cf. 'Agda.Utils.Null.ifNull'.
caseList :: [a] -> b -> (a -> [a] -> b) -> b
caseList xs n c = listCase n c xs

-- | Case distinction for lists, with list first.
--   Cf. 'Agda.Utils.Null.ifNull'.
caseListM :: Monad m => m [a] -> m b -> (a -> [a] -> m b) -> m b
caseListM mxs n c = listCase n c =<< mxs

-- | Case distinction for lists, with list last.
listCase :: b -> (a -> [a] -> b) -> [a] -> b
listCase n c []     = n
listCase n c (x:xs) = c x xs

-- | Head function (safe).
headMaybe :: [a] -> Maybe a
headMaybe = listToMaybe

-- | Head function (safe). Returns a default value on empty lists.
--
-- > headWithDefault 42 []      = 42
-- > headWithDefault 42 [1,2,3] = 1
headWithDefault :: a -> [a] -> a
headWithDefault def = fromMaybe def . headMaybe

-- | Tail function (safe).
tailMaybe :: [a] -> Maybe [a]
tailMaybe = fmap snd . uncons

-- | Tail function (safe).  Returns a default list on empty lists.
tailWithDefault :: [a] -> [a] -> [a]
tailWithDefault def = fromMaybe def . tailMaybe

-- | Last element (safe).
lastMaybe :: [a] -> Maybe a
lastMaybe [] = Nothing
lastMaybe xs = Just $ last xs

-- | Last two elements (safe).
last2 :: [a] -> Maybe (a, a)
last2 (x : y : xs) = Just $ loop x y xs
  where
  loop x y []     = (x, y)
  loop x y (z:xs) = loop y z xs
last2 _ = Nothing

-- | Drop from the end of a list.
--   @dropEnd n = reverse . drop n . reverse@
--   (Forces the whole list even for @n==0@.)
dropEnd :: forall a. Int -> [a] -> [a]
dropEnd n = snd . foldr f (n, [])
  where
  f :: a -> (Int, [a]) -> (Int, [a])
  f x (n, xs)
    | n <= 0    = (0, x:xs)
    | otherwise = (n-1, xs)

-- | Opposite of cons @(:)@, safe.
uncons :: [a] -> Maybe (a, [a])
uncons []     = Nothing
uncons (x:xs) = Just (x,xs)

-- | Maybe cons.   @mcons ma as = maybeToList ma ++ as@
mcons :: Maybe a -> [a] -> [a]
mcons ma as = maybe as (:as) ma

-- | 'init' and 'last' in one go, safe.
initLast :: [a] -> Maybe ([a],a)
initLast []     = Nothing
initLast (a:as) = Just $ loop a as where
  loop a []      = ([], a)
  loop a (b : bs) = mapFst (a:) $ loop b bs

-- | init, safe.
initMaybe :: [a] -> Maybe [a]
initMaybe = fmap fst . initLast

-- | Lookup function (partially safe).
(!!!) :: [a] -> Int -> Maybe a
[]       !!! _         = Nothing
(x : _)  !!! 0         = Just x
(_ : xs) !!! n         = xs !!! (n - 1)

-- | Lookup function with default value for index out of range.
--   The name is chosen akin to 'Data.List.genericIndex'.
indexWithDefault :: a -> [a] -> Int -> a
indexWithDefault a []       _ = a
indexWithDefault a (x : _)  0 = x
indexWithDefault a (_ : xs) n = indexWithDefault a xs (n - 1)

-- | Find an element satisfying a predicate and return it with its index.
--   TODO: more efficient implementation!?
findWithIndex :: (a -> Bool) -> [a] -> Maybe (a, Int)
findWithIndex p as = headMaybe $ filter (p . fst) $ zip as [0..]

-- | downFrom n = [n-1,..1,0]
downFrom :: Integral a => a -> [a]
downFrom n | n <= 0     = []
           | otherwise = let n' = n-1 in n' : downFrom n'

-- | Update the first element of a list, if it exists.
updateHead :: (a -> a) -> [a] -> [a]
updateHead f [] = []
updateHead f (a : as) = f a : as

-- | Update the last element of a list, if it exists.
updateLast :: (a -> a) -> [a] -> [a]
updateLast f [] = []
updateLast f [a] = [f a]
updateLast f (a : as@(_ : _)) = a : updateLast f as

-- | Update nth element of a list, if it exists.
--   Precondition: the index is >= 0.
updateAt :: Int -> (a -> a) -> [a] -> [a]
updateAt _ f [] = []
updateAt 0 f (a : as) = f a : as
updateAt n f (a : as) = a : updateAt (n-1) f as

-- | A generalized version of @partition@.
--   (Cf. @mapMaybe@ vs. @filter@).
mapEither :: (a -> Either b c) -> [a] -> ([b],[c])
{-# INLINE mapEither #-}
mapEither f xs = foldr (deal f) ([],[]) xs

deal :: (a -> Either b c) -> a -> ([b],[c]) -> ([b],[c])
deal f a ~(bs,cs) = case f a of
  Left  b -> (b:bs, cs)
  Right c -> (bs, c:cs)

-- | Split off the largest suffix whose elements satisfy a predicate.
--
--   @spanEnd p xs = (ys, zs)@
--   where @xs = ys ++ zs@
--   and @all p zs@
--   and @maybe True (not . p) (lastMaybe yz)@.
spanEnd :: forall a. (a -> Bool) -> [a] -> ([a], [a])
spanEnd p = snd . foldr f (True, ([], []))
  where
  f :: a -> (Bool, ([a], [a])) -> (Bool, ([a], [a]))
  f x (b', (xs, ys)) = (b, if b then (xs, x:ys) else (x:xs, ys))
    where b = b' && p x

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

-- | Like 'filter', but additionally return the last partition
--   of the list where the predicate is @False@ everywhere.
filterAndRest :: (a -> Bool) -> [a] -> ([a],[a])
filterAndRest p = mapMaybeAndRest $ \ a -> if p a then Just a else Nothing

-- | Like 'mapMaybe', but additionally return the last partition
--   of the list where the function always returns @Nothing@.
mapMaybeAndRest :: (a -> Maybe b) -> [a] -> ([b],[a])
mapMaybeAndRest f = loop [] where
  loop acc = \case
    []                   -> ([], reverse acc)
    x:xs | Just y <- f x -> first (y:) $ loop [] xs
         | otherwise     -> loop (x:acc) xs

-- | Drops from both lists simultaneously until one list is empty.
dropCommon :: [a] -> [b] -> ([a],[b])
dropCommon (x : xs) (y : ys) = dropCommon xs ys
dropCommon xs ys = (xs, ys)

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
stripPrefixBy :: (a -> a -> Bool) -> Prefix a -> [a] -> Maybe (Suffix a)
stripPrefixBy eq = loop
  where
  loop []    rest = Just rest
  loop (_:_) []   = Nothing
  loop (p:pat) (r:rest)
    | eq p r    = loop pat rest
    | otherwise = Nothing

-- | @stripSuffix suf xs = Just pre@ iff @xs = pre ++ suf@.
stripSuffix :: Eq a => Suffix a -> [a] -> Maybe (Prefix a)
stripSuffix [] = Just
stripSuffix s  = stripReversedSuffix (reverse s)

type ReversedSuffix a = [a]

-- | @stripReversedSuffix rsuf xs = Just pre@ iff @xs = pre ++ reverse suf@.
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

-- | A variant of 'List.groupBy' which applies the predicate to consecutive
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

-- | @'groupOn' f = 'groupBy' (('==') \`on\` f) '.' 'List.sortBy' ('compare' \`on\` f)@.

groupOn :: Ord b => (a -> b) -> [a] -> [[a]]
groupOn f = List.groupBy ((==) `on` f) . List.sortBy (compare `on` f)

-- | @splitExactlyAt n xs = Just (ys, zs)@ iff @xs = ys ++ zs@
--   and @genericLength ys = n@.
splitExactlyAt :: Integral n => n -> [a] -> Maybe ([a], [a])
splitExactlyAt 0 xs       = return ([], xs)
splitExactlyAt n []       = Nothing
splitExactlyAt n (x : xs) = mapFst (x :) <$> splitExactlyAt (n-1) xs

-- | A generalised variant of 'elemIndex'.

genericElemIndex :: (Eq a, Integral i) => a -> [a] -> Maybe i
genericElemIndex x xs =
  listToMaybe $
  map fst $
  filter snd $
  zip [0..] $
  map (== x) xs

-- | Requires both lists to have the same length.
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


-- | Efficient variant of 'nubBy' for finite lists.
--
-- Specification:
--
-- > nubOn f xs == 'nubBy' ((==) `'on'` f) xs.
nubOn :: Ord b => (a -> b) -> [a] -> [a]
nubOn tag =
  map snd
  . List.sortBy (compare `on` fst)
  . map (snd . head)
  . List.groupBy ((==) `on` fst)
  . List.sortBy (compare `on` fst)
  . map (\p@(_, x) -> (tag x, p))
  . zip [1..]

-- | Efficient variant of 'nubBy' for finite lists.
--
-- Specification: For each list @xs@ there is a list @ys@ which is a
-- permutation of @xs@ such that
--
-- > uniqOn f xs == 'nubBy' ((==) `'on'` f) ys.
--
-- Furthermore
--
-- > List.sortBy (compare `on` f) (uniqOn f xs) == uniqOn f xs.
uniqOn :: Ord b => (a -> b) -> [a] -> [a]
uniqOn key = Map.elems . Map.fromList . map (\ a -> (key a, a))

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

editDistanceSpec :: Eq a => [a] -> [a] -> Int
editDistanceSpec [] ys = length ys
editDistanceSpec xs [] = length xs
editDistanceSpec (x : xs) (y : ys)
  | x == y    = editDistanceSpec xs ys
  | otherwise = 1 + minimum [ editDistanceSpec (x : xs) ys
                            , editDistanceSpec xs (y : ys)
                            , editDistanceSpec xs ys ]

editDistance :: Eq a => [a] -> [a] -> Int
editDistance xs ys = editD 0 0
  where xss = List.tails xs
        yss = List.tails ys
        tbl = Map.fromList [ ((i, j), editD' i j) | i <- [0..length xss - 1], j <- [0..length yss - 1] ]
        editD i j = tbl Map.! (i, j)
        editD' i j =
          case (xss !! i, yss !! j) of
            ([], ys) -> length ys
            (xs, []) -> length xs
            (x : xs, y : ys)
              | x == y    -> editD (i + 1) (j + 1)
              | otherwise -> 1 + minimum [ editD (i + 1) j, editD i (j + 1), editD (i + 1) (j + 1) ]
