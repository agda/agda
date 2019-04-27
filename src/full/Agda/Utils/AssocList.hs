
-- | Additional functions for association lists.

module Agda.Utils.AssocList where

import Prelude hiding (lookup)

import qualified Data.List as List
import Data.Function

import Agda.Utils.Tuple

import Agda.Utils.Impossible

-- | A finite map, represented as a set of pairs.
--
--   Invariant: at most one value per key.
type AssocList k v = [(k,v)]

-- | O(n).
--   Reexport 'List.lookup'.
lookup :: Eq k => k -> AssocList k v -> Maybe v
lookup = List.lookup

-- | O(n).
--   Get the domain (list of keys) of the finite map.
keys :: AssocList k v -> [k]
keys = map fst

-- | O(1).
--   Add a new binding.
--   Assumes the binding is not yet in the list.
insert :: k -> v -> AssocList k v -> AssocList k v
insert k v = ((k,v) :)

-- | O(n).
--   Update the value at a key.
--   The key must be in the domain of the finite map.
--   Otherwise, an internal error is raised.
update :: Eq k => k -> v -> AssocList k v -> AssocList k v
update k v = updateAt k $ const v

-- | O(n).
--   Delete a binding.
--   The key must be in the domain of the finite map.
--   Otherwise, an internal error is raised.
delete :: Eq k => k -> AssocList k v -> AssocList k v
delete k = List.deleteBy ((==) `on` fst) (k, __IMPOSSIBLE__)

-- | O(n).
--   Update the value at a key with a certain function.
--   The key must be in the domain of the finite map.
--   Otherwise, an internal error is raised.
updateAt :: Eq k => k -> (v -> v) -> AssocList k v -> AssocList k v
updateAt k f = loop where
  loop []       = __IMPOSSIBLE__
  loop (p@(k',v) : ps)
    | k == k'   = (k, f v) : ps
    | otherwise = p : loop ps

-- | O(n).
--   Map over an association list, preserving the order.
mapWithKey :: (k -> v -> v) -> AssocList k v -> AssocList k v
mapWithKey f = map $ \ (k,v) -> (k, f k v)

-- | O(n).
--   If called with a effect-producing function, violation of the invariant
--   could matter here (duplicating effects).
mapWithKeyM :: Applicative m => (k -> v -> m v) -> AssocList k v -> m (AssocList k v)
mapWithKeyM f = mapM $ \ (k,v) -> (k,) <$> f k v
  where
    -- mapM is applicative!
    mapM g [] = pure []
    mapM g (x : xs) = (:) <$> g x <*> mapM g xs

-- | O(n).
--   Named in analogy to 'Data.Map.mapKeysMonotonic'.
--   To preserve the invariant, it is sufficient that the key
--   transformation is injective (rather than monotonic).
mapKeysMonotonic :: (k -> k') -> AssocList k v -> AssocList k' v
mapKeysMonotonic f = map $ mapFst f
