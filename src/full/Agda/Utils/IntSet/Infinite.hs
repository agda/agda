{-# LANGUAGE CPP #-}
-- |  Possibly infinite sets of integers (but with finitely many consecutive
--    segments). Used for checking guard coverage in int/nat cases in the
--    treeless compiler.
module Agda.Utils.IntSet.Infinite
  ( IntSet
  , empty, full, below, above, singleton
  , difference, member, toFiniteList
  , invariant )
  where

#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup hiding (All(..))
#endif

import Data.Set (Set)
import qualified Data.Set as Set

-- | Represents a set of integers.
--   Invariants:
--     - All cannot be the argument to `Below` or `Above`
--     - at most one 'IntsBelow'
--     - at most one 'IntsAbove'
--     - if `Below lo` and `Below hi`, then `lo < hi`
--     - if `Below lo .. (Some xs)` then `all (> lo) xs`
--     - if `Above hi .. (Some xs)` then `all (< hi - 1) xs`
data IntSet = All
              | Some (Set Integer)
              | Below Integer IntSet  -- exclusive
              | Above Integer IntSet  -- inclusive
  deriving (Show)

instance Eq IntSet where
  r == r' = norm r == norm r'
    where
      norm All          = Nothing
      norm (Some xs)    = Just (Nothing, Nothing, xs)
      norm (Below lo r) = do (_, hi, xs) <- norm r; return (Just lo, hi, xs)
      norm (Above hi r) = do (lo, _, xs) <- norm r; return (lo, Just hi, xs)

below' :: Integer -> IntSet -> IntSet
below' _  All = All
below' lo r@(Some xs)
  | lo `Set.member` xs = below' (lo + 1) r
  | otherwise  = Below lo $ Some $ Set.filter (>= lo) xs
below' lo r0@(Below lo' r)
  | lo' >= lo = r0
  | otherwise = below' lo r
below' lo (Above hi r)
  | hi <= lo  = All
  | otherwise = Above hi $ below' lo r

above' :: Integer -> IntSet -> IntSet
above' _  All = All
above' hi r@(Some xs)
  | (hi - 1) `Set.member` xs = above' (hi - 1) r
  | otherwise        = Above hi $ Some $ Set.filter (< hi) xs
above' hi r0@(Above hi' r)
  | hi' <= hi = r0
  | otherwise = above' hi r
above' hi (Below lo r)
  | hi <= lo  = All
  | otherwise = Below lo $ above' hi r

some' :: Set Integer -> IntSet -> IntSet
some' xs r | null xs = r
some' xs (Some ys) = Some (Set.union xs ys)
some' _  All = All
some' xs (Below lo r)
  | lo `Set.member` xs = some' xs (Below (lo + 1) r)
  | otherwise  = below' lo $ some' (Set.filter (>= lo) xs) r
some' xs (Above hi r)
  | (hi - 1) `Set.member` xs = some' xs (Above (hi - 1) r)
  | otherwise        = above' hi $ some' (Set.filter (< hi) xs) r

difference :: IntSet -> IntSet -> IntSet
difference r All           = empty
difference r (Some xs)     = subtractSome r xs
difference r (Below lo r') = difference (subtractBelow r lo) r'
difference r (Above hi r') = difference (subtractAbove r hi) r'

subtractSome :: IntSet -> Set Integer -> IntSet
subtractSome r xs | null xs = r
subtractSome All xs = below lo <> above hi <> Some (Set.fromList [lo..hi - 1] `Set.difference` xs)
  where lo = minimum xs
        hi = maximum xs + 1
subtractSome (Some ys) xs = Some (Set.difference ys xs)
subtractSome (Below lo r) xs = Below (min lo lo') $ subtractSome (Some (Set.fromList [lo'..lo - 1]) <> r) xs
  where lo' = minimum xs
subtractSome (Above hi r) xs = Above (max hi hi') $ subtractSome (Some (Set.fromList [hi..hi' - 1]) <> r) xs
  where hi' = maximum xs + 1

subtractBelow :: IntSet -> Integer -> IntSet
subtractBelow All           lo = above lo
subtractBelow (Below lo' r) lo = some' (Set.fromList [lo..lo' - 1]) (subtractBelow r lo)
subtractBelow (Above hi r)  lo = Above (max hi lo) (subtractBelow r lo)
subtractBelow (Some xs)     lo = Some $ Set.filter (>= lo) xs

subtractAbove :: IntSet -> Integer -> IntSet
subtractAbove All           hi = below hi
subtractAbove (Above hi' r) hi = some' (Set.fromList [hi'..hi - 1]) (subtractAbove r hi)
subtractAbove (Below lo r)  hi = Below (min lo hi) (subtractAbove r hi)
subtractAbove (Some xs)     hi = Some $ Set.filter (< hi) xs

instance Semigroup IntSet where
  Below lo r <> r' = below' lo (r <> r')
  Above hi r <> r' = above' hi (r <> r')
  Some xs    <> r' = some' xs r'
  All        <> _  = All

instance Monoid IntSet where
  mempty  = empty
  mappend = (<>)

-- | Membership
member :: Integer -> IntSet -> Bool
member _ All          = True
member x (Some xs)    = Set.member x xs
member x (Below lo s) = x < lo  || member x s
member x (Above hi s) = x >= hi || member x s

-- | All integers `< n`
below :: Integer -> IntSet
below lo = Below lo empty

-- | All integers `>= n`
above :: Integer -> IntSet
above hi = Above hi empty

-- | A single integer.
singleton :: Integer -> IntSet
singleton x = fromList [x]

-- | From a list of integers.
fromList :: [Integer] -> IntSet
fromList xs = Some (Set.fromList xs)

-- | No integers.
empty :: IntSet
empty = Some Set.empty

-- | All integers.
full :: IntSet
full = All

-- | If finite, return the list of elements.
toFiniteList :: IntSet -> Maybe [Integer]
toFiniteList (Some xs) = Just $ Set.toList xs
toFiniteList All       = Nothing
toFiniteList Above{}   = Nothing
toFiniteList Below{}   = Nothing

-- | Invariant.
invariant :: IntSet -> Bool
invariant xs =
  case xs of
    All         -> True
    Some{}      -> True
    Below lo ys -> invariant ys && invBelow lo ys
    Above hi ys -> invariant ys && invAbove hi ys
  where
    invBelow lo All          = False
    invBelow lo (Some xs)    = all (> lo) xs
    invBelow lo Below{}      = False
    invBelow lo (Above hi r) = lo < hi && invBelow lo r

    invAbove hi All          = False
    invAbove hi (Some xs)    = all (< hi - 1) xs
    invAbove hi Above{}      = False
    invAbove hi (Below lo r) = lo < hi && invAbove hi r

