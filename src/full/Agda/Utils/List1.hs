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

{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
  -- because of https://gitlab.haskell.org/ghc/ghc/issues/10339

module Agda.Utils.List1
  ( module Agda.Utils.List1
  , module List1
  ) where

import Control.Arrow ((&&&))
import qualified Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty as List1 hiding (NonEmpty)

import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Data.Semigroup as Semigroup

import Agda.Utils.Null (Null(..))

type List1 = Data.List.NonEmpty.NonEmpty

-- | Return the last element and the rest.

initLast :: List1 a -> ([a], a)
initLast = List1.init &&& List1.last
  -- traverses twice, but does not create intermediate pairs

-- | Append a list to a non-empty list.

append :: List1 a -> [a] -> List1 a
append (x :| xs) ys = x :| mappend xs ys

-- | Prepend a list to a non-empty list.

prepend :: [a] -> List1 a -> List1 a
prepend as bs = foldr (<|) bs as

-- | More precise type for @snoc@.

snoc :: [a] -> a -> List1 a
snoc as a = prepend as $ a :| []

-- | Concatenate one or more non-empty lists.

concat :: [List1 a] -> [a]
concat = concatMap toList

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
