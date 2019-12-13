-- | Semirings.

module Agda.Termination.Semiring
  ( HasZero(..)
  , Semiring(..)
  , integerSemiring
  , intSemiring
  , boolSemiring
  ) where



-- | @HasZero@ is needed for sparse matrices, to tell which is the element
--   that does not have to be stored.
--   It is a cut-down version of @SemiRing@ which is definable
--   without the implicit @?cutoff@.
class Eq a => HasZero a where
  zeroElement :: a

-- | Semirings.

data Semiring a = Semiring
  { add  :: a -> a -> a  -- ^ Addition.
  , mul  :: a -> a -> a  -- ^ Multiplication.
  , zero :: a            -- ^ Zero.
  -- The one is never used in matrix multiplication
  -- , one  :: a            -- ^ One.
  }

------------------------------------------------------------------------
-- Specific semirings

-- | The standard semiring on 'Integer's.

instance HasZero Integer where
  zeroElement = 0

integerSemiring :: Semiring Integer
integerSemiring = Semiring { add = (+), mul = (*), zero = 0 } -- , one = 1 }

-- | The standard semiring on 'Int's.

instance HasZero Int where
  zeroElement = 0

intSemiring :: Semiring Int
intSemiring = Semiring { add = (+), mul = (*), zero = 0 } -- , one = 1 }

-- | The standard semiring on 'Bool's.

boolSemiring :: Semiring Bool
boolSemiring =
  Semiring { add = (||), mul = (&&), zero = False } --, one = True }
