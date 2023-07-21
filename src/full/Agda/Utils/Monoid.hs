{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE CPP  #-}

-- | More monoids.

module Agda.Utils.Monoid where

#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup (Semigroup(..))
#endif


-- | Maximum of on-negative (small) natural numbers.

newtype MaxNat = MaxNat { getMaxNat :: Int }
  deriving (Num, Eq, Ord, Show, Enum)

instance Semigroup MaxNat where
  (<>) = max

instance Monoid MaxNat where
  mempty     = 0
#if !(MIN_VERSION_base(4,11,0))
  mappend    = (<>)
#endif
  mconcat [] = 0
  mconcat ms = maximum ms
