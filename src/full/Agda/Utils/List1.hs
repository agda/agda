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
  ) where

import Prelude hiding (filter)

import Control.Arrow ((&&&))
import Control.Monad (filterM)
import qualified Control.Monad as List (zipWithM, zipWithM_)

import qualified Data.Either as Either
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Data.Semigroup as Semigroup

import qualified Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty as List1 hiding (NonEmpty)

import Agda.Utils.Functor ((<.>))
import Agda.Utils.Null (Null(..))
import qualified Agda.Utils.List as List

type List1 = Data.List.NonEmpty.NonEmpty

-- | Return the last element and the rest.

initLast :: List1 a -> ([a], a)
initLast = List1.init &&& List1.last
  -- traverses twice, but does not create intermediate pairs

-- | Build a list with one element.

#if !(MIN_VERSION_base(4,15,0))
singleton :: a -> List1 a
singleton = (:| [])
#endif

-- | Append a list to a non-empty list.

append :: List1 a -> [a] -> List1 a
append (x :| xs) ys = x :| mappend xs ys

-- | Prepend a list to a non-empty list.

prepend :: [a] -> List1 a -> List1 a
prepend as bs = foldr (<|) bs as

-- | More precise type for @snoc@.

snoc :: [a] -> a -> List1 a
snoc as a = prepend as $ a :| []

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

-- | Concatenate one or more non-empty lists.

concat :: [List1 a] -> [a]
concat = concatMap toList

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

-- | Like 'List1.filter'.

mapMaybe :: (a -> Maybe b) -> List1 a -> [b]
mapMaybe f = Maybe.mapMaybe f . List1.toList

-- | Like 'Data.Either.partitionEithers'.

partitionEithers :: List1 (Either a b) -> ([a], [b])
partitionEithers = Either.partitionEithers . List1.toList

-- | Like 'Data.Either.lefts'.

lefts :: List1 (Either a b) -> [a]
lefts = Either.lefts  . List1.toList

-- | Like 'Data.Either.rights'.

rights :: List1 (Either a b) -> [b]
rights = Either.rights  . List1.toList


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
