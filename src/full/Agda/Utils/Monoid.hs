{-# OPTIONS_GHC -Wunused-imports #-}

-- | More monoids.

module Agda.Utils.Monoid where

-- | Maximum of on-negative (small) natural numbers.

newtype MaxNat = MaxNat { getMaxNat :: Int }
  deriving (Num, Eq, Ord, Show, Enum)

instance Semigroup MaxNat where
  (<>) = max

instance Monoid MaxNat where
  mempty     = 0
  mconcat [] = 0
  mconcat ms = maximum ms
