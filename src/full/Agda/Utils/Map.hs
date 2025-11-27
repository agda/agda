{-# LANGUAGE CPP #-}

module Agda.Utils.Map where

import Control.Monad ((<$!>))
import Data.Functor.Compose
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Map.Internal (Map(..), balanceL, balanceR, singleton)
import Data.Maybe (mapMaybe)

import Agda.Utils.Impossible

-- * Monadic map operations
---------------------------------------------------------------------------

{-# INLINE insertWithGood #-}
-- | Version of `insertWith` that's willing to be properly inlined.
insertWithGood :: forall k a. Ord k => (a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWithGood f k !a = go k a where
  go :: k -> a -> Map k a -> Map k a
  go !kx x Tip               = singleton kx x
  go  kx x (Bin sy ky y l r) = case compare kx ky of
    LT -> balanceL ky y (go kx x l) r
    GT -> balanceR ky y l (go kx x r)
    EQ -> let !y' = f x y in Bin sy kx y' l r

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
