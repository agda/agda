module Agda.Utils.HashMap
  ( module HashMap
  ) where

import Data.HashMap.Strict as HashMap

-- ASR (20 January 2016) Issue 1779: I removed the @mapMaybe@ and
-- @alter@ functions because them currently aren't used and
-- them were added in unordered-containers 0.2.6.0.

-- mapMaybe :: (a -> Maybe b) -> HashMap k a -> HashMap k b

-- alter :: (Eq k, Hashable k) =>
--          (Maybe a -> Maybe a) -> k -> HashMap k a -> HashMap k a
