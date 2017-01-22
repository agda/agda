{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | More monoids.

module Agda.Utils.Monoid where

import Data.Monoid

-- | Maximum of on-negative (small) natural numbers.

newtype MaxNat = MaxNat { getMaxNat :: Int }
  deriving (Num, Eq, Ord, Show, Enum)

instance Monoid MaxNat where
  mempty     = 0
  mappend    = max
  mconcat [] = 0
  mconcat ms = maximum ms
