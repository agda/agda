-- | Semirings.

module Agda.Termination.Semiring
  ( HasZero(..), SemiRing(..)
  , Semiring(..)
  , semiringInvariant
  , integerSemiring
  , intSemiring
  , boolSemiring
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


-- | @HasZero@ is needed for sparse matrices, to tell which is the element
--   that does not have to be stored.
--   It is a cut-down version of @SemiRing@ which is definable
--   without the implicit @?cutoff@.
class Eq a => HasZero a where
  zeroElement :: a

-- | Semirings.

data Semiring a
  = Semiring { add  :: a -> a -> a  -- ^ Addition.
             , mul  :: a -> a -> a  -- ^ Multiplication.
             , zero :: a            -- ^ Zero.
-- The one is never used in matrix multiplication
--             , one  :: a            -- ^ One.
             }

-- | Semiring invariant.

-- I think it's OK to use the same x, y, z triple for all the
-- properties below.

semiringInvariant :: Eq a
                  => Semiring a
                  -> a -> a -> a -> Bool
semiringInvariant (Semiring { add = (+), mul = (*)
                            , zero = zero --, one = one
                            }) = \x y z ->
  associative (+)           x y z &&
  identity zero (+)         x     &&
  commutative (+)           x y   &&
  associative (*)           x y z &&
--  identity one (*)          x     &&
  leftDistributive (*) (+)  x y z &&
  rightDistributive (*) (+) x y z &&
  isZero zero (*)           x

------------------------------------------------------------------------
-- Specific semirings

-- | The standard semiring on 'Integer's.

instance HasZero Integer where
  zeroElement = 0

integerSemiring :: Semiring Integer
integerSemiring = Semiring { add = (+), mul = (*), zero = 0 } -- , one = 1 }

prop_integerSemiring :: Integer -> Integer -> Integer -> Bool
prop_integerSemiring = semiringInvariant integerSemiring

-- | The standard semiring on 'Int's.

instance HasZero Int where
  zeroElement = 0

intSemiring :: Semiring Int
intSemiring = Semiring { add = (+), mul = (*), zero = 0 } -- , one = 1 }

prop_intSemiring :: Int -> Int -> Int -> Bool
prop_intSemiring = semiringInvariant intSemiring

-- | The standard semiring on 'Bool's.

boolSemiring :: Semiring Bool
boolSemiring =
  Semiring { add = (||), mul = (&&), zero = False } --, one = True }

prop_boolSemiring :: Bool -> Bool -> Bool -> Bool
prop_boolSemiring = semiringInvariant boolSemiring

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Termination.Semiring"
  [ quickCheck' prop_integerSemiring
  , quickCheck' prop_boolSemiring
  ]
