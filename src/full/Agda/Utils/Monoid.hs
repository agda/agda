{-# LANGUAGE CPP  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | More monoids.

module Agda.Utils.Monoid where

#if !(MIN_VERSION_base(4,11,0))
import Data.Semigroup (Semigroup(..))
#endif


-- | Maximum of on-negative (small) natural numbers.

newtype MaxNat = MaxNat { getMaxNat :: Int }
  deriving (Num, Eq, Ord, Show, Enum)

instance Semigroup MaxNat where
  {-# INLINE (<>) #-}
  (<>) = max

instance Monoid MaxNat where
  {-# INLINE mempty #-}
  mempty     = 0
#if !(MIN_VERSION_base(4,11,0))
  {-# INLINE mappend #-}
  mappend    = (<>)
#endif
  mconcat [] = 0
  mconcat ms = maximum ms
