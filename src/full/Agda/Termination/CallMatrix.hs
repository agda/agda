{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE ImplicitParams             #-}
{-# LANGUAGE CPP                        #-}

module Agda.Termination.CallMatrix where

-- module Agda.Termination.CallMatrix
--   ( CallMatrix'(..), CallMatrix
--   , callMatrix
--   , CallComb(..)
--   , tests
--   ) where

#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif

import Agda.Termination.CutOff
import Agda.Termination.Order as Order
import Agda.Termination.SparseMatrix as Matrix
import Agda.Termination.Semiring (HasZero(..))

import Agda.Utils.Favorites (Favorites)
import qualified Agda.Utils.Favorites as Fav

import Agda.Utils.Null
import Agda.Utils.PartialOrd
import Agda.Utils.Pretty
import Agda.Utils.Singleton

------------------------------------------------------------------------
--  * Call matrices
------------------------------------------------------------------------

-- | Call matrix indices = function argument indices.
--
--   Machine integer 'Int' is sufficient, since we cannot index more arguments
--   than we have addresses on our machine.

type ArgumentIndex = Int

-- | Call matrices.
--
--   A call matrix for a call @f --> g@ has dimensions @ar(g) × ar(f)@.
--
--   Each column corresponds to one formal argument of caller @f@.
--   Each row corresponds to one argument in the call to @g@.
--
--   In the presence of dot patterns, a call argument can be related
--   to /several/ different formal arguments of @f@.
--
--   See e.g. @test/succeed/DotPatternTermination.agda@:
--
--   @
--     data D : Nat -> Set where
--       cz : D zero
--       c1 : forall n -> D n -> D (suc n)
--       c2 : forall n -> D n -> D n
--
--     f : forall n -> D n -> Nat
--     f .zero    cz        = zero
--     f .(suc n) (c1  n d) = f n (c2 n d)
--     f n        (c2 .n d) = f n d
--   @
--
--   Call matrices (without guardedness) are
--
--   @
--           -1 -1   n < suc n  and       n <  c1 n d
--            ?  =                   c2 n d <= c1 n d
--
--            = -1   n <= n     and  n < c2 n d
--            ? -1                   d < c2 n d
--   @
--
--   Here is a part of the original documentation for call matrices
--   (kept for historical reasons):
--
--   This datatype encodes information about a single recursive
--   function application. The columns of the call matrix stand for
--   'source' function arguments (patterns). The rows of the matrix stand for
--   'target' function arguments. Element @(i, j)@ in the matrix should
--   be computed as follows:
--
--     * 'Order.lt' (less than) if the @j@-th argument to the 'target'
--       function is structurally strictly smaller than the @i@-th
--       pattern.
--
--     * 'Order.le' (less than or equal) if the @j@-th argument to the
--       'target' function is structurally smaller than the @i@-th
--       pattern.
--
--     * 'Order.unknown' otherwise.


newtype CallMatrix' a = CallMatrix { mat :: Matrix ArgumentIndex a }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, PartialOrd)

type CallMatrix = CallMatrix' Order

deriving instance NotWorse CallMatrix

instance HasZero a => Diagonal (CallMatrix' a) a where
  diagonal = diagonal . mat


-- | Call matrix multiplication and call combination.

class CallComb a where
  (>*<) :: (?cutoff :: CutOff) => a -> a -> a

-- | Call matrix multiplication.
--
--   @f --(m1)--> g --(m2)--> h@  is combined to @f --(m2 `mul` m1)--> h@
--
--   Note the reversed order of multiplication:
--   The matrix @c1@ of the second call @g-->h@ in the sequence
--   @f-->g-->h@ is multiplied with the matrix @c2@ of the first call.
--
--   Preconditions:
--   @m1@ has dimensions @ar(g) × ar(f)@.
--   @m2@ has dimensions @ar(h) × ar(g)@.
--
--   Postcondition:
--   @m1 >*< m2@ has dimensions @ar(h) × ar(f)@.

instance CallComb CallMatrix where
  CallMatrix m1 >*< CallMatrix m2 = CallMatrix $ mul orderSemiring m2 m1

{- UNUSED, BUT DON'T REMOVE!
-- | Call matrix addition = minimum = pick worst information.
addCallMatrices :: (?cutoff :: CutOff) => CallMatrix -> CallMatrix -> CallMatrix
addCallMatrices cm1 cm2 = CallMatrix $
  add (Semiring.add orderSemiring) (mat cm1) (mat cm2)
-}

------------------------------------------------------------------------
-- * Call matrix augmented with path information.
------------------------------------------------------------------------

-- | Call matrix augmented with path information.

data CallMatrixAug cinfo = CallMatrixAug
  { augCallMatrix :: CallMatrix -- ^ The matrix of the (composed call).
  , augCallInfo   :: cinfo      -- ^ Meta info, like call path.
  }
  deriving (Eq, Show)

instance Diagonal (CallMatrixAug cinfo) Order where
  diagonal = diagonal . augCallMatrix

instance PartialOrd (CallMatrixAug cinfo) where
  comparable m m' = comparable (augCallMatrix m) (augCallMatrix m')

instance NotWorse (CallMatrixAug cinfo) where
  c1 `notWorse` c2 = augCallMatrix c1 `notWorse` augCallMatrix c2

-- | Augmented call matrix multiplication.

instance Monoid cinfo => CallComb (CallMatrixAug cinfo) where
  CallMatrixAug m1 p1 >*< CallMatrixAug m2 p2 =
    CallMatrixAug (m1 >*< m2) (mappend p1 p2)

-- | Non-augmented call matrix.

noAug :: Monoid cinfo => CallMatrix -> CallMatrixAug cinfo
noAug m = CallMatrixAug m mempty

------------------------------------------------------------------------
-- * Sets of incomparable call matrices augmented with path information.
------------------------------------------------------------------------

-- | Sets of incomparable call matrices augmented with path information.
--   Use overloaded 'null', 'empty', 'singleton', 'mappend'.
newtype CMSet cinfo = CMSet { cmSet :: Favorites (CallMatrixAug cinfo) }
  deriving ( Show, Semigroup, Monoid, Null, Singleton (CallMatrixAug cinfo) )

-- | Call matrix set product is the Cartesian product.

instance Monoid cinfo => CallComb (CMSet cinfo) where
  CMSet as >*< CMSet bs = CMSet $ Fav.fromList $
    [ a >*< b | a <- Fav.toList as, b <- Fav.toList bs ]

-- | Insert into a call matrix set.

insert :: CallMatrixAug cinfo -> CMSet cinfo -> CMSet cinfo
insert a (CMSet as) = CMSet $ Fav.insert a as

-- | Union two call matrix sets.

union :: CMSet cinfo -> CMSet cinfo -> CMSet cinfo
union = mappend
-- union (CMSet as) (CMSet bs) = CMSet $ Fav.union as bs

-- | Convert into a list of augmented call matrices.

toList :: CMSet cinfo -> [CallMatrixAug cinfo]
toList (CMSet as) = Fav.toList as

------------------------------------------------------------------------
-- * Printing
------------------------------------------------------------------------

instance Pretty CallMatrix where
  pretty (CallMatrix m) = pretty m

instance Pretty cinfo => Pretty (CallMatrixAug cinfo) where
  pretty (CallMatrixAug m cinfo) = pretty cinfo $$ pretty m

instance Pretty cinfo => Pretty (CMSet cinfo) where
  pretty = vcat . punctuate newLine . map pretty . toList
    where newLine = "\n"
