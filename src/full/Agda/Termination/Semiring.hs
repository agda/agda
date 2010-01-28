-- {-# LANGUAGE UndecidableInstances #-}

-- | Semirings.

module Agda.Termination.Semiring
  ( SemiRing(..)
  , Semiring(..)
  , semiringInvariant
  , Agda.Termination.Semiring.tests
  ) where

import Data.Monoid

import Agda.Utils.QuickCheck
import Agda.Utils.TestHelpers

{- | SemiRing type class.  Additive monoid with multiplication operation.
Inherit addition and zero from Monoid. -}

class (Eq a, Monoid a) => SemiRing a where
--  isZero   :: a -> Bool
  multiply :: a -> a -> a


-- | Semirings.

class Semiring a where
  add  :: a -> a -> a  -- ^ Addition.
  mul  :: a -> a -> a  -- ^ Multiplication.
  zero :: a            -- ^ Zero.
  one  :: a            -- ^ One.

-- | Semiring invariant.

-- I think it's OK to use the same x, y, z triple for all the
-- properties below.

semiringInvariant :: (Arbitrary a, Eq a, Show a, Semiring a)
                  => a -> a -> a -> Bool
semiringInvariant = \x y z ->
  associative add           x y z &&
  identity zero add         x     &&
  commutative add           x y   &&
  associative mul           x y z &&
  identity one mul          x     &&
  leftDistributive mul add  x y z &&
  rightDistributive mul add x y z &&
  isZero zero mul           x

------------------------------------------------------------------------
-- Specific semirings

-- | The standard semiring on 'Integer's.

instance Monoid Integer where
  mempty = 0
  mappend = (+)

instance SemiRing Integer where 
  multiply = (*)
    

integerSemiring :: Semiring Integer
integerSemiring = Semiring { add = (+), mul = (*), zero = 0 } -- , one = 1 }

prop_integerSemiring = semiringInvariant integerSemiring

-- | The standard semiring on 'Bool's.

instance Semiring Bool where
  add  = (||)
  mul  = (&&)
  zero = False
  one  = True

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Termination.Semiring"
  [ quickCheck' (semiringInvariant
                   :: Integer -> Integer -> Integer -> Bool)
  , quickCheck' (semiringInvariant :: Bool -> Bool -> Bool -> Bool)
  ]
