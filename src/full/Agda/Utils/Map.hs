{-# LANGUAGE CPP #-}

module Agda.Utils.Map where

import Control.Monad ((<$!>))

import Data.Functor.Compose
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Map.Internal (Map(..), balanceL, balanceR, singleton)
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set

import Agda.Utils.Impossible

-- * Monadic map operations
---------------------------------------------------------------------------

{-# INLINE insertWithGood #-}
-- | Version of `insertWith` that's willing to be properly inlined. The extra @c@ argument
--   is passed down to the insertions unchanged. It can be used to avoid closure creation
--   for the loop.
insertWithGood :: forall k a c. Ord k => (c -> a -> a -> a) -> c -> k -> a -> Map k a -> Map k a
insertWithGood f c k !a = go c k a where
  go :: c -> k -> a -> Map k a -> Map k a
  go !c !kx x Tip               = singleton kx x
  go  c  kx x (Bin sy ky y l r) = case compare kx ky of
    LT -> balanceL ky y (go c kx x l) r
    GT -> balanceR ky y l (go c kx x r)
    EQ -> let !y' = f c x y in Bin sy kx y' l r

{-# INLINE forGood_ #-}
-- | Version of `forM_` that deigns to be properly lambda-lifted for State, Reader, etc.
forGood_ :: forall k v m. Applicative m => Map k v -> (v -> m ()) -> m ()
forGood_ m f = go m where
  go Tip             = pure ()
  go (Bin _ k v l r) = go l *> f v *> go r

{-# INLINE forWithKey_ #-}
forWithKey_ :: forall k v m. Applicative m => Map k v -> (k -> v -> m ()) -> m ()
forWithKey_ m f = go m where
  go Tip             = pure ()
  go (Bin _ k v l r) = go l *> f k v *> go r

{-# INLINE adjustM #-}
-- | Update monadically the value at one position (must exist!).
adjustM :: (Functor f, Ord k) => (v -> f v) -> k -> Map k v -> f (Map k v)
adjustM f = Map.alterF $ \case
  Nothing -> __IMPOSSIBLE__
  Just v  -> Just <$> f v

{-# INLINE adjustM' #-}
-- | Wrapper for 'adjustM' for convenience.
adjustM' :: (Functor f, Ord k) => (v -> f (a, v)) -> k -> Map k v -> f (a, Map k v)
adjustM' f k = getCompose . adjustM (Compose . f) k

-- * Non-monadic map operations
---------------------------------------------------------------------------

#if !MIN_VERSION_containers(0,8,0)
{-# INLINE filterKeys #-}
-- | Filter a map based on the keys.
filterKeys :: (k -> Bool) -> Map k a -> Map k a
filterKeys p = Map.filterWithKey (const . p)
#endif

-- | Filter a map and rewrite the keys.
mapKeysMaybe :: Ord k => (k -> Maybe k) -> Map k a -> Map k a
mapKeysMaybe f = Map.fromList . mapMaybe (\ (k, a) -> (, a) <$> f k) . Map.toList

-- | Check whether a map is a singleton.
isSingleMap :: Map k v -> Maybe (k, v)
isSingleMap (Bin 1 k v _ _) = Just (k, v)
isSingleMap _               = Nothing

-- | @partitionKeys m s = 'Map.partition' (`Set.member` s) m@
-- but with potential for efficient implementation.
partitionKeys :: Ord k => Map k a -> Set k -> (Map k a, Map k a)
partitionKeys m s = (Map.restrictKeys m s, Map.withoutKeys m s)

-- | @partitionMap m m' = 'Map.partition' (`Map.member` m') m@
-- but with potential for efficient implementation.
partitionMap :: Ord k => Map k a -> Map k b -> (Map k a, Map k a)
partitionMap m = partitionKeys m . Map.keysSet
