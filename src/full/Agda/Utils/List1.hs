{-# LANGUAGE CPP #-}

-- | Non-empty lists.
--
--   Better name @List1@ for non-empty lists, plus missing functionality.
--
--   Import:
--   @
--
--     {-# LANGUAGE PatternSynonyms #-}
--
--     import           Agda.Utils.List1 (List1, pattern (:|))
--     import qualified Agda.Utils.List1 as List1
--
--   @

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
  -- because of https://gitlab.haskell.org/ghc/ghc/issues/10339

module Agda.Utils.List1
  ( module Agda.Utils.List1
  , module List1
  , module IsList
  ) where

import Prelude hiding (filter)

import Control.Arrow ((&&&))
import Control.Monad (filterM)
import qualified Control.Monad as List (zipWithM, zipWithM_)

import qualified Data.Either as Either
import Data.Function ( on )
import qualified Data.List as List
import qualified Data.Maybe as Maybe

import Data.List.NonEmpty as List1 hiding (fromList, toList)
import qualified Data.List.NonEmpty as List1 (toList)

import GHC.Exts as IsList ( IsList(..) )

import Agda.Utils.Functor ((<.>), (<&>))
import Agda.Utils.Null (Null(..))
import qualified Agda.Utils.List as List

-- Set up doctest.
-- $setup
-- >>> :seti -XOverloadedLists

type List1 = NonEmpty
type String1 = List1 Char

-- | Lossless 'toList', opposite of 'nonEmpty'.
--
toList' :: Maybe (List1 a) -> [a]
toList' = maybe [] toList

-- | Safe version of 'Data.List.NonEmpty.fromList'.

fromListSafe
  :: List1 a  -- ^ Default value if convertee is empty.
  -> [a]      -- ^ List to convert, supposedly non-empty.
  -> List1 a  -- ^ Converted list.
fromListSafe err   [] = err
fromListSafe _ (x:xs) = x :| xs

-- | Return the last element and the rest.

initLast :: List1 a -> ([a], a)
initLast = List1.init &&& List1.last
  -- traverses twice, but does not create intermediate pairs

-- | Last two elements (safe).
--   O(n).
last2 :: List1 a -> Maybe (a, a)
last2 (x :| y : xs) = Just $ List.last2' x y xs
last2 _ = Nothing

-- | Build a list with one element.

#if !(MIN_VERSION_base(4,15,0))
singleton :: a -> List1 a
singleton = (:| [])
#endif

#if !MIN_VERSION_base(4,16,0)
-- | Append a list to a non-empty list.

appendList :: List1 a -> [a] -> List1 a
appendList (x :| xs) ys = x :| mappend xs ys

-- | Prepend a list to a non-empty list.

prependList :: [a] -> List1 a -> List1 a
prependList as bs = Prelude.foldr (<|) bs as
#endif

-- | More precise type for @snoc@.

snoc :: [a] -> a -> List1 a
snoc as a = prependList as $ a :| []

-- | @'groupOn' f = 'groupBy' (('==') \`on\` f) '.' 'List.sortBy' ('compare' \`on\` f)@.
-- O(n log n).
groupOn :: Ord b => (a -> b) -> [a] -> [List1 a]
groupOn f = List1.groupBy ((==) `on` f) . List.sortBy (compare `on` f)

groupOn1 :: Ord b => (a -> b) -> List1 a -> List1 (List1 a)
groupOn1 f = List1.groupBy1 ((==) `on` f) . List1.sortBy (compare `on` f)

-- | More precise type for 'Agda.Utils.List.groupBy''.
--
-- A variant of 'List.groupBy' which applies the predicate to consecutive
-- pairs.
-- O(n).
groupBy' :: forall a. (a -> a -> Bool) -> [a] -> [List1 a]
groupBy' _ []           = []
groupBy' p xxs@(x : xs) = grp x $ List.zipWith (\ x y -> (p x y, y)) xxs xs
  where
  grp :: a -> [(Bool,a)] -> [List1 a]
  grp x ys
    | let (xs, rest) = List.span fst ys
    = (x :| List.map snd xs) : case rest of
      []                 -> []
      ((_false, z) : zs) -> grp z zs

-- | Group consecutive items that share the same first component.
--
groupByFst :: forall a b. Eq a => [(a,b)] -> [(a, List1 b)]
groupByFst =
    List.map (\ ((tag, b) :| xs) -> (tag, b :| List.map snd xs))
      -- Float the grouping to the top level
  . List1.groupBy ((==) `on` fst)
      -- Group together characters in the same role.

-- | Group consecutive items that share the same first component.
--
groupByFst1 :: forall a b. Eq a => List1 (a, b) -> List1 (a, List1 b)
groupByFst1 =
    fmap (\ ((tag, b) :| xs) -> (tag, b :| List.map snd xs))
      -- Float the grouping to the top level
  . List1.groupBy1 ((==) `on` fst)
      -- Group together characters in the same role.

-- | Split a list into sublists. Generalisation of the prelude function
--   @words@.
--   Same as 'Data.List.Split.wordsBy' and 'Data.List.Extra.wordsBy',
--   but with the non-emptyness guarantee on the chunks.
--   O(n).
--
--   > words xs == wordsBy isSpace xs
wordsBy :: (a -> Bool) -> [a] -> [List1 a]
wordsBy p = loop
  where
  loop as = case List.dropWhile p as of
    []   -> []
    x:xs -> (x :| ys) : loop zs where (ys, zs) = List.break p xs

-- | Breaks a list just /after/ an element satisfying the predicate is
--   found.
--
--   >>> breakAfter even [1,3,5,2,4,7,8]
--   (1 :| [3,5,2],[4,7,8])

breakAfter :: (a -> Bool) -> List1 a -> (List1 a, [a])
breakAfter p (x :| xs) = List.breakAfter1 p x xs

-- | Concatenate one or more non-empty lists.

concat :: [List1 a] -> [a]
concat = concatMap toList

concatMap1 :: (a -> List1 b) -> List1 a -> List1 b
concatMap1 = (=<<)

-- | Like 'Data.List.union'.  Duplicates in the first list are not removed.
-- O(nm).
union :: Eq a => List1 a -> List1 a -> List1 a
union (a :| as) bs = a :| List.union as (filter (/= a) bs)

-- * Recovering non-emptyness.

ifNull :: [a] -> b -> (List1 a -> b) -> b
ifNull []       b _ = b
ifNull (a : as) _ f = f $ a :| as

ifNotNull :: [a] -> (List1 a -> b) -> b -> b
ifNotNull []       _ b = b
ifNotNull (a : as) f _ = f $ a :| as

unlessNull :: Null m => [a] -> (List1 a -> m) -> m
unlessNull []       _ = empty
unlessNull (x : xs) f = f $ x :| xs

-- * List functions with no special behavior for non-empty lists.

-- | Checks if all the elements in the list are equal. Assumes that
--   the 'Eq' instance stands for an equivalence relation.
--   O(n).
allEqual :: Eq a => List1 a -> Bool
allEqual (x :| xs) = all (== x) xs

-- | Like 'Maybe.catMaybes'.

catMaybes :: List1 (Maybe a) -> [a]
catMaybes =  Maybe.catMaybes . List1.toList

-- | Like 'Maybe.mapMaybe'.

mapMaybe :: (a -> Maybe b) -> List1 a -> [b]
mapMaybe f = Maybe.mapMaybe f . List1.toList

-- | Like 'List.find'.

find :: (a -> Bool) -> List1 a -> Maybe a
find f = List.find f . List1.toList

-- | Like 'Data.Either.partitionEithers'.

partitionEithers :: List1 (Either a b) -> ([a], [b])
partitionEithers = Either.partitionEithers . List1.toList

-- | Like 'Data.Either.lefts'.

lefts :: List1 (Either a b) -> [a]
lefts = Either.lefts  . List1.toList

-- | Like 'Data.Either.rights'.

rights :: List1 (Either a b) -> [b]
rights = Either.rights  . List1.toList

-- | Like 'Data.List.unwords'.

unwords :: List1 String -> String
unwords = List.unwords . List1.toList

-- | Non-efficient, monadic 'nub'.
-- O(n²).
nubM :: Monad m => (a -> a -> m Bool) -> List1 a -> m (List1 a)
nubM eq (a :| as) = (a :|) <$> do List.nubM eq =<< filterM (not <.> eq a) as

-- | Like 'Control.Monad.zipWithM'.

zipWithM :: Applicative m => (a -> b -> m c) -> List1 a -> List1 b -> m (List1 c)
zipWithM f (a :| as) (b :| bs) = (:|) <$> f a b <*> List.zipWithM f as bs

-- | Like 'Control.Monad.zipWithM'.

zipWithM_ :: Applicative m => (a -> b -> m c) -> List1 a -> List1 b -> m ()
zipWithM_ f (a :| as) (b :| bs) = f a b *> List.zipWithM_ f as bs

-- | List 'Data.List.foldr' but with a base case for the singleton list.

foldr :: (a -> b -> b) -> (a -> b) -> List1 a -> b
foldr f g (x :| xs) = loop x xs
  where
  loop x []       = g x
  loop x (y : ys) = f x $ loop y ys

-- | Update the first element of a non-empty list.
--   O(1).
updateHead :: (a -> a) -> List1 a -> List1 a
updateHead f (a :| as) = f a :| as

-- | Update the last element of a non-empty list.
--   O(n).
updateLast :: (a -> a) -> List1 a -> List1 a
updateLast f (a :| as) = loop a as
  where
  loop a []       = singleton $ f a
  loop a (b : bs) = cons a $ loop b bs

-- | Focus on the first element of a non-empty list.
--   O(1).
lensHead :: Functor f => (a -> f a) -> List1 a -> f (List1 a)
lensHead f (a :| as) = f a <&> (:| as)

-- | Focus on the last element of a non-empty list.
--   O(n).
lensLast :: Functor f => (a -> f a) -> List1 a -> f (List1 a)
lensLast f (a :| as) = loop a as
  where
  loop a []       = singleton <$> f a
  loop a (b : bs) = cons a <$> loop b bs
