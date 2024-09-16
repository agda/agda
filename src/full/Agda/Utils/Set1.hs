-- | Non-empty sets.
--
--   Provides type @Set1@ of non-empty sets.
--
--   Import:
--   @
--
--     import           Agda.Utils.Set1 (Set1)
--     import qualified Agda.Utils.Set1 as Set1
--
--   @

module Agda.Utils.Set1
  ( module Agda.Utils.Set1
  , module Set1
  ) where

import Data.Set (Set)
import Data.Set.NonEmpty as Set1

type Set1 = Set1.NESet

ifNull :: Set a -> b -> (Set1 a -> b) -> b
ifNull s b f = Set1.withNonEmpty b f s

-- | A more general type would be @Null m => Set a -> (Set1 a -> m) -> m@
--   but this type is problematic as we do not have a general
--   @instance Applicative m => Null (m ())@.
--
unlessNull :: Applicative m => Set a -> (Set1 a -> m ()) -> m ()
unlessNull = flip $ Set1.withNonEmpty $ pure ()
{-# INLINE unlessNull #-}

unlessNullM :: Monad m => m (Set a) -> (Set1 a -> m ()) -> m ()
unlessNullM m k = m >>= (`unlessNull` k)
{-# INLINE unlessNullM #-}
