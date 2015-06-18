module Agda.Utils.HashMap
  ( module HashMap
  , mapMaybe
  , alter
  ) where

import Data.Hashable
import Data.HashMap.Strict as HashMap
import qualified Data.Maybe as Maybe

-- | Like 'Data.Map.Strict.mapMaybe'.

-- This code has not been benchmarked. Other implementations may be
-- more efficient.

mapMaybe :: (a -> Maybe b) -> HashMap k a -> HashMap k b
mapMaybe f = fmap Maybe.fromJust . HashMap.filter Maybe.isJust . fmap f

-- | Like 'Data.Map.Strict.alter'.

alter :: (Eq k, Hashable k) =>
         (Maybe a -> Maybe a) -> k -> HashMap k a -> HashMap k a
alter f k m = case HashMap.lookup k m of
  Nothing -> case f Nothing of
    Nothing -> m
    Just v  -> HashMap.insert k v m
  Just v  -> case f (Just v) of
    Nothing -> HashMap.delete k m
    Just v  -> HashMap.insert k v m
