{-# LANGUAGE CPP #-}

{-# OPTIONS_GHC -Wno-dodgy-exports #-} -- don't complain about empty exports for Agda.Utils.IArray

-- | Array utilities.

module Agda.Utils.IArray (module Agda.Utils.IArray, module Data.Array.IArray) where

import Data.Array.IArray
import Data.Array.Base   ( IArray(..) )
import Data.Ix           ( inRange )

import GHC.Ix            ( unsafeIndex )

-- Backported from array-0.5.6:

#if !MIN_VERSION_array(0,5,6)

{-# INLINE (!?) #-}
-- | Returns 'Just' the element of an immutable array at the specified index,
-- or 'Nothing' if the index is out of bounds.
--
(!?) :: (IArray a e, Ix i) => a i e -> i -> Maybe e
(!?) arr i
  | inRange b i = Just $ unsafeAt arr $ unsafeIndex b i
  | otherwise   = Nothing
  where b = bounds arr

#endif
