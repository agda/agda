{-# LANGUAGE CPP, ImplicitParams, TypeSynonymInstances, FlexibleInstances,
  MultiParamTypeClasses,
  GeneralizedNewtypeDeriving, StandaloneDeriving, DeriveFunctor,
  DeriveFoldable, DeriveTraversable #-}

module Agda.Termination.CallMatrix
  ( CallMatrix'(..), CallMatrix
  , cmMul
  , callMatrix
  , tests
  ) where

import Data.List as List hiding (union, insert)
import Data.Foldable (Foldable)
import qualified Data.Foldable as Fold
import Data.Traversable (Traversable)
import qualified Data.Traversable as Trav

import Agda.Termination.Order hiding (tests)
import Agda.Termination.SparseMatrix as Matrix hiding (tests)
import Agda.Termination.Semiring (HasZero(..), Semiring)
import qualified Agda.Termination.Semiring as Semiring

import Agda.Utils.Monad
import Agda.Utils.PartialOrd
import Agda.Utils.QuickCheck
import Agda.Utils.TestHelpers

------------------------------------------------------------------------
-- Call matrices

-- | Call matrix indices.
--
--   Machine integer 'Int' is sufficient, since we cannot index more than
--   we have addresses on our machine.

type Index = Int

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

newtype CallMatrix' a = CallMatrix { mat :: Matrix Index a }
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, CoArbitrary, PartialOrd)

type CallMatrix = CallMatrix' Order

deriving instance NotWorse CallMatrix

instance HasZero a => Diagonal (CallMatrix' a) a where
  diagonal = diagonal . mat

-- | Call matrix multiplication.
--
-- Precondition: see 'Matrix.mul'.

cmMul :: (?cutoff :: CutOff) => CallMatrix -> CallMatrix -> CallMatrix
cm1 `cmMul` cm2 =
  CallMatrix { mat = mul orderSemiring (mat cm1) (mat cm2) }

{- UNUSED, BUT DON'T REMOVE!
-- | Call matrix addition = minimum = pick worst information.
addCallMatrices :: (?cutoff :: CutOff) => CallMatrix -> CallMatrix -> CallMatrix
addCallMatrices cm1 cm2 = CallMatrix $
  add (Semiring.add orderSemiring) (mat cm1) (mat cm2)
-}

------------------------------------------------------------------------
-- CallMatrix: Generators and tests

instance Arbitrary CallMatrix where
  arbitrary = callMatrix =<< arbitrary

-- | Generates a call matrix of the given size.

callMatrix :: Size Index -> Gen CallMatrix
callMatrix sz = CallMatrix <$> matrix sz

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Termination.CallMatrix"
  [
  ]
  where ?cutoff = DontCutOff -- CutOff 2  -- don't cut off in tests!


-- RETIRED:  LONG OUTDATED call matrix invariant

-- -- | In a call matrix at most one element per row may be different
-- -- from 'unknown'.

-- callMatrixInvariant :: CallMatrix -> Bool
-- callMatrixInvariant (CallMatrix m) =
--   matrixInvariant m &&
--   all ((<= 1) . length . filter (/= unknown)) (toLists m)

-- prop_Arbitrary_CallMatrix = callMatrixInvariant

-- -- | Generates a call matrix of the given size.

-- callMatrix :: Size Index -> Gen CallMatrix
-- callMatrix sz = do
--   m <- matrixUsingRowGen sz rowGen
--   return $ CallMatrix { mat = m }
--   where
--   rowGen :: Index -> Gen [Order]
--   rowGen 0 = return []
--   rowGen n = do
--     x <- arbitrary
--     i <- choose (0, n - 1)
--     return $ genericReplicate i unknown ++ [x] ++
--              genericReplicate (n - 1 - i) unknown

-- prop_callMatrix sz =
--   forAll (callMatrix sz) $ \cm ->
--     callMatrixInvariant cm
--     &&
--     size (mat cm) == sz

-- prop_cmMul sz =
--   forAll natural $ \c2 ->
--   forAll (callMatrix sz) $ \cm1 ->
--   forAll (callMatrix $ Size { rows = cols sz, cols = c2 }) $ \cm2 ->
--     callMatrixInvariant (cm1 `cmMul` cm2)

-- tests :: IO Bool
-- tests = runTests "Agda.Termination.CallMatrix"
--   [ quickCheck' callMatrixInvariant
--   , quickCheck' prop_Arbitrary_CallMatrix
--   , quickCheck' prop_callMatrix
--   , quickCheck' prop_cmMul
--   ]
--   where ?cutoff = DontCutOff -- CutOff 2  -- don't cut off in tests!


