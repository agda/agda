{-# LANGUAGE CPP #-}

module Agda.Utils.Map where

import Data.Functor.Compose
import Data.Map (Map)
import qualified Data.Map as Map

import Agda.Utils.Impossible

-- * Monadic map operations
---------------------------------------------------------------------------

-- | Update monadically the value at one position (must exist!).
adjustM :: (Functor f, Ord k) => (v -> f v) -> k -> Map k v -> f (Map k v)
adjustM f = Map.alterF $ \case
  Nothing -> __IMPOSSIBLE__
  Just v  -> Just <$> f v

-- | Wrapper for 'adjustM' for convenience.
adjustM' :: (Functor f, Ord k) => (v -> f (a, v)) -> k -> Map k v -> f (a, Map k v)
adjustM' f k = getCompose . adjustM (Compose . f) k

-- * Non-monadic map operations
---------------------------------------------------------------------------

#if !MIN_VERSION_containers(0,8,0)
-- | Filter a map based on the keys.
filterKeys :: (k -> Bool) -> Map k a -> Map k a
filterKeys p = Map.filterWithKey (const . p)
#endif

-- | Check whether a map is a singleton.
isSingleMap :: Map k v -> Maybe (k, v)
isSingleMap m
  | Map.size m == 1  -- This is fast since the size is cached.
  , [(k,v)] <- Map.toList m = Just (k, v)
  | otherwise = Nothing
