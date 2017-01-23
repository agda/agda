{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | More monoids.

module Agda.Utils.Monoid where

import Data.Semigroup (Semigroup(..))
import Data.Monoid (Monoid(..))

-- | Maximum of on-negative (small) natural numbers.

newtype MaxNat = MaxNat { getMaxNat :: Int }
  deriving (Num, Eq, Ord, Show, Enum)

instance Semigroup MaxNat where
  (<>) = max

instance Monoid MaxNat where
  mempty     = 0
  mappend    = (<>)
  mconcat [] = 0
  mconcat ms = maximum ms
