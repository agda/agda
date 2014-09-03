{-# LANGUAGE CPP #-}
{-# LANGUAGE TupleSections #-}

-- | Additional functions for association lists.

module Agda.Utils.AssocList where

import Data.Functor

#include "../undefined.h"
import Agda.Utils.Impossible

-- | A finite map, represented as a set of pairs.
--
--   Invariant: at most one value per key.
type AssocList k v = [(k,v)]

-- | Update the value at a key.
--   The key must be in the domain of the finite map.
--   Otherwise, an internal error is raised.
update :: Eq k => k -> v -> AssocList k v -> AssocList k v
update k v = updateAt k $ const v

-- | Update the value at a key with a certain function.
--   The key must be in the domain of the finite map.
--   Otherwise, an internal error is raised.
updateAt :: Eq k => k -> (v -> v) -> AssocList k v -> AssocList k v
updateAt k f = loop where
  loop []       = __IMPOSSIBLE__
  loop (p@(k',v) : ps)
    | k == k'   = (k, f v) : ps
    | otherwise = p : loop ps

-- | Map over an association list, preserving the order.
mapWithKey :: (k -> v -> v) -> AssocList k v -> AssocList k v
mapWithKey f = map $ \ (k,v) -> (k, f k v)

mapWithKeyM :: (Functor m, Monad m) => (k -> v -> m v) -> AssocList k v -> m (AssocList k v)
mapWithKeyM f = mapM $ \ (k,v) -> (k,) <$> f k v

