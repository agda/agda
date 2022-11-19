{-# LANGUAGE CPP             #-}

-- | Some functions, generators and instances suitable for writing
-- QuickCheck properties.

module Internal.Helpers
  ( module Internal.Helpers
  , module Test.QuickCheck
    -- * Tasty framework functions
  , testGroup
  , testProperties
  , testProperty
  , TestTree
  ) where

import Control.Monad

import qualified Control.Monad.Fail as Fail

import Data.Functor
import Data.Semigroup        ( (<>), Semigroup )
import Test.QuickCheck
import Test.Tasty            ( testGroup, TestName, TestTree )
import Test.Tasty.QuickCheck ( testProperties, testProperty )

import Agda.Utils.Functor
import Agda.Utils.List1      ( List1, pattern (:|) )
import qualified Agda.Utils.List1 as List1
import Agda.Utils.PartialOrd
import Agda.Utils.POMonoid

import Agda.Utils.Impossible

------------------------------------------------------------------------
-- QuickCheck helpers

quickCheck' :: Testable prop => prop -> IO Bool
quickCheck' p = fmap isSuccess $ quickCheckResult p

quickCheckWith' :: Testable prop => Args -> prop -> IO Bool
quickCheckWith' args p = fmap isSuccess $ quickCheckWithResult args p

------------------------------------------------------------------------
-- Helpers for type signatures of algebraic properties.

-- | Binary operator.

type BinOp a = a -> a -> a

-- | Property over 1 variable.

type Prop1     a = a -> Bool
type Property1 a = a -> Property

-- | Property over 2 variables.

type Prop2     a = a -> a -> Bool
type Property2 a = a -> a -> Property

-- | Property over 3 variables.

type Prop3     a = a -> a -> a -> Bool
type Property3 a = a -> a -> a -> Property

-- | Property over 4 variables.

type Prop4     a = a -> a -> a -> a -> Bool
type Property4 a = a -> a -> a -> a -> Property

------------------------------------------------------------------------
-- Algebraic properties

-- | Is the operator associative?

isAssociative :: Eq a => BinOp a -> Prop3 a
isAssociative (+) = \ x y z ->
  x + (y + z) == (x + y) + z

-- | Is the operator commutative?

isCommutative :: Eq a => BinOp a -> Prop2 a
isCommutative (+) = \ x y ->
  x + y == y + x

-- | Is the operator idempotent?

isIdempotent :: Eq a => BinOp a -> Prop1 a
isIdempotent (/\) = \ x ->
  (x /\ x) == x

-- | Is the element a zero for the operator?

isZero :: Eq a => a -> BinOp a -> Prop1 a
isZero zer (*) = \ x ->
  (zer * x == zer)
  &&
  (x * zer == zer)

-- | Is the element a unit for the operator?

isIdentity :: Eq a => a -> BinOp a -> Prop1 a
isIdentity one (*) = \ x ->
  (one * x == x)
  &&
  (x * one == x)

-- | Does the first operator distribute (from the left) over the second one?

isLeftDistributive :: Eq a => BinOp a -> BinOp a -> Prop3 a
isLeftDistributive (*) (+) = \ x y z ->
  x * (y + z) == (x * y) + (x * z)

-- | Does the first operator distribute (from the right) over the second one?

isRightDistributive :: Eq a => BinOp a -> BinOp a -> Prop3 a
isRightDistributive (*) (+) = \ x y z ->
  (x + y) * z == (x * z) + (y * z)

-- | Does the first operator distribute over the second one?

isDistributive :: Eq a => BinOp a -> BinOp a -> Prop3 a
isDistributive (*) (+) = \ x y z ->
  isLeftDistributive (*) (+) x y z &&
  isRightDistributive (*) (+) x y z

-- | Does the operator satisfy the semigroup law?

isSemigroup :: (Eq a, Semigroup a) => Prop3 a
isSemigroup = isAssociative (<>)

-- | Does the operator satisfy the monoid laws?

isMonoid :: (Eq a, Semigroup a, Monoid a) => Property3 a
isMonoid x y z =
-- ASR (2017-01-25): What if `mappend ≠ (<>)`? It isn't possible
-- because we are using the `-Wnoncanonical-monoid-instances` flag.
  isSemigroup x y z .&&.
  isIdentity mempty mappend x

isSemigroupMorphism :: (Eq b, Semigroup a, Semigroup b) => (a -> b) -> Prop2 a
isSemigroupMorphism f = \ x y ->
  f (x <> y) == f x <> f y

-- | Monoid morphism where the source monoid is given by a unit and a multiplication.
isMonoidMorphismUnder :: (Eq b, Monoid b) => a -> (a -> a -> a) -> (a -> b) -> Property2 a
isMonoidMorphismUnder one (*) f = \ x y ->
  f one == mempty
  .&&.
  f (x * y) == f x `mappend` f y

isMonoidMorphism :: (Eq b, Monoid a, Monoid b) => (a -> b) -> Property2 a
isMonoidMorphism = isMonoidMorphismUnder mempty mappend

-- | The semiring is given by an additive monoid, a unit and a multiplication.
isSemimodule :: (Eq m, Monoid r, Monoid m) => r -> (r -> r -> r) -> (r -> m -> m)
  -> r -> r -> Property2 m
isSemimodule one (*) op r s m n =
  isMonoidMorphism (op r) m n
  .&&.
  isMonoidMorphism (`op` m) r s
  .&&.
  -- isMonoidMorphismUnder one (*) (Endo . op) r s  -- Problem: no Eq Endo
  -- expand to points:
  op one m == m
  .&&.
  op (r * s) m == op r (op s m)

-- | The semiring is given by an additive monoid, a unit and a multiplication.
isAlmostSemimodule :: (Eq m, Semigroup r, Monoid r, Semigroup m, Monoid m) => r -> (r -> r -> r) -> (r -> m -> m)
  -> r -> r -> Property2 m
isAlmostSemimodule one (*) op r s m n =
  isMonoidMorphism (op r) m n
  .&&.
  isSemigroupMorphism (`op` m) r s
  .&&.
  -- isMonoidMorphismUnder one (*) (Endo . op) r s  -- Problem: no Eq Endo
  -- expand to points:
  op one m == m
  .&&.
  op (r * s) m == op r (op s m)

-- | Is the semigroup operation monotone in both arguments
--   wrt. to the associated partial ordering?
--   We state this with only three variables to get fewer discarded tests.
isMonotoneComposition :: (Eq a, POSemigroup a) => Property3 a
isMonotoneComposition x x' y =
  related x POLE x' ==> related (x <> y) POLE (x' <> y) && related (y <> x) POLE (y <> x')

-- | Do the semigroup operation and the inverse composition form
--   a Galois connection?

isGaloisConnection :: (Eq a, Semigroup a, LeftClosedPOMonoid a) => Prop3 a
isGaloisConnection p x y =
  related (inverseCompose p x) POLE y == related x POLE (p <> y)

------------------------------------------------------------------------
-- Generators

-- | Generates natural numbers.

natural :: (Integral i) => Gen i
natural = fromInteger . abs <$> arbitrary

-- | Generates positive numbers.

positive :: (Integral i) => Gen i
positive = succ <$> natural

-- | Generates a list of elements picked from a given list.
listOfElements :: [a] -> Gen [a]
listOfElements [] = return []
listOfElements xs = listOf $ elements xs

-- | Generates an officially non-empty list, while 'listOf1' does it inofficially.
list1Of :: Gen a -> Gen (List1 a)
list1Of = List1.fromListSafe undefined <.> listOf1

-- | If the given list is non-empty, then an element from the list is
-- generated, and otherwise an arbitrary element is generated.

elementsUnlessEmpty :: Arbitrary a => [a] -> Gen a
elementsUnlessEmpty [] = arbitrary
elementsUnlessEmpty xs = elements xs

-- | Generates values of 'Maybe' type, using the given generator to
-- generate the contents of the 'Just' constructor.

maybeGen :: Gen a -> Gen (Maybe a)
maybeGen gen = frequency [ (1, return Nothing)
                         , (9, Just <$> gen)
                         ]

-- | 'Coarbitrary' \"generator\" for 'Maybe'.

maybeCoGen :: (a -> Gen b -> Gen b) -> (Maybe a -> Gen b -> Gen b)
maybeCoGen f Nothing  = variant 0
maybeCoGen f (Just x) = variant 1 . f x

-- | Generates two elements.

two :: Gen a -> Gen (a, a)
two gen = liftM2 (,) gen gen

-- | Generates three elements.

three :: Gen a -> Gen (a, a, a)
three gen = liftM3 (,,) gen gen gen

-- | \"Resizes\" a generator.

smaller
  :: Int  -- ^ This number must not be 0.
  -> Gen a
  -> Gen a
smaller k g = sized $ \ n -> resize (1 + div n k) g

------------------------------------------------------------------------
-- Instances

instance Fail.MonadFail Gen where
  fail = error

instance Arbitrary a => Arbitrary (List1 a) where
  arbitrary = List1.fromListSafe __IMPOSSIBLE__ . getNonEmpty <$> arbitrary
  shrink = map (List1.fromListSafe __IMPOSSIBLE__ . getNonEmpty) . shrink . (NonEmpty . List1.toList)

instance CoArbitrary a => CoArbitrary (List1 a) where
  coarbitrary (x :| xs) = coarbitrary (x, xs)

------------------------------------------------------------------------
-- Test driver

-- | Runs the tests, and returns 'True' if all tests were successful.

runTests :: String    -- ^ A label for the tests. Used for
                      --   informational purposes.
         -> [IO Bool]
         -> IO Bool
runTests name tests = do
  putStrLn name
  and <$> sequence tests
