-- | Non-empty maps.
--
--   Provides type @Map1@ of non-empty maps.
--
--   Import:
--   @
--
--     import Agda.Utils.Map1 (Map1)
--     import Agda.Utils.Map1 qualified as Map1
--
--   @

module Agda.Utils.Map1
  ( module Agda.Utils.Map1
  , module Map1
  ) where

import Data.Map (Map)
import Data.Map.NonEmpty as Map1

type Map1 = Map1.NEMap

ifNull :: Map k a -> b -> (Map1 k a -> b) -> b
ifNull s b f = Map1.withNonEmpty b f s

-- | A more general type would be @Null m => Map k a -> (Map1 k a -> m) -> m@
--   but this type is problematic as we do not have a general
--   @instance Applicative m => Null (m ())@.
--
unlessNull :: Applicative m => Map k a -> (Map1 k a -> m ()) -> m ()
unlessNull = flip $ Map1.withNonEmpty $ pure ()
{-# INLINE unlessNull #-}

unlessNullM :: Monad m => m (Map k a) -> (Map1 k a -> m ()) -> m ()
unlessNullM m k = m >>= (`unlessNull` k)
{-# INLINE unlessNullM #-}

-- | Map both keys and values where the map is monotonic for the keys.
--
-- A function that maps both keys and values while preserving
-- the map structure is missing in "Data.Map.NonEmpty".
-- We implement it simplistically here
-- as a combination of 'Map1.mapKeysMonotonic' and 'fmap'.
mapKeysAndValuesMonotonic :: (k -> k) -> (a -> b) -> Map1 k a -> Map1 k b
mapKeysAndValuesMonotonic f g = Map1.mapKeysMonotonic f . fmap g
