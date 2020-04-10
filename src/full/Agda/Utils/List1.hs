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

import qualified Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty as List1 hiding (NonEmpty)

import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified Data.Semigroup as Semigroup

import Agda.Utils.Null (Null(..))

type List1 = Data.List.NonEmpty.NonEmpty

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

concat :: List1 (List1 a) -> List1 a
concat = foldr1 (Semigroup.<>)

-- | Like 'List1.filter'.

mapMaybe :: (a -> Maybe b) -> List1 a -> [b]
mapMaybe f = Maybe.mapMaybe f . List1.toList

-- * Recovering non-emptyness.

ifNull :: [a] -> b -> (List1 a -> b) -> b
ifNull []       b _ = b
ifNull (a : as) _ f = f $ a :| as

unlessNull :: Null m => [a] -> (List1 a -> m) -> m
unlessNull []       _ = empty
unlessNull (x : xs) f = f $ x :| xs
