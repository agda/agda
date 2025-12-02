module Agda.Utils.Set (module Agda.Utils.Set, module Data.Set) where

import Data.Set
import Data.Set.Internal (Set(Tip, Bin))

-- Adapted from rejected pull request to containers
-- https://github.com/haskell/containers/pull/291

-- | /O(log n)/. Find the given element and return the copy contained in the set.
lookupKey :: Ord a => a -> Set a -> Maybe a
lookupKey !x = go
  where
    go Tip = Nothing
    go (Bin _ y l r) = case compare x y of
      LT -> go l
      GT -> go r
      EQ -> Just y
