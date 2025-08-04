{-# OPTIONS_GHC -Wunused-imports #-}

-- | More monoids.

module Agda.Utils.Monoid
  ( MaxNat(..)
  , Fwd, pattern Fwd, appFwd
  )
  where

import Data.Monoid (Endo(..), Dual(..))

-- | Maximum of on-negative (small) natural numbers.

newtype MaxNat = MaxNat { getMaxNat :: Int }
  deriving (Num, Eq, Ord, Show, Enum)

instance Semigroup MaxNat where
  (<>) = max

instance Monoid MaxNat where
  mempty     = 0
  mconcat [] = 0
  mconcat ms = maximum ms

-- | Function composition in the diagrammatic order.

newtype Fwd a = MkFwd (Dual (Endo a))
  deriving (Semigroup, Monoid)

pattern Fwd :: (a -> a) -> Fwd a
pattern Fwd f = MkFwd (Dual (Endo f))

appFwd :: Fwd a -> (a -> a)
appFwd (MkFwd (Dual (Endo f))) = f
