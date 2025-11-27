module Agda.Utils.IntMap (module Agda.Utils.IntMap, module Data.IntMap) where

import Data.IntMap

{-# INLINE forWithKey_ #-}
forWithKey_ :: forall v m. Applicative m => IntMap v -> (Int -> v -> m ()) -> m ()
forWithKey_ m f = foldrWithKey (\ k v act -> f k v *> act) (pure ()) m
