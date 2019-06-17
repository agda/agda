{-# LANGUAGE CPP             #-}

-- | Some functions, generators and instances suitable for writing
-- QuickCheck properties.

module Internal.Helpers
  ( -- * QuickCheck helpers
    quickCheck'
  , quickCheckWith'
    -- * QuickCheck module
  , module Test.QuickCheck
    -- * Algebraic properties
  , isAssociative
  , isCommutative
  , isIdempotent
  , isZero
  , isIdentity
  , isLeftDistributive
  , isRightDistributive
  , isDistributive
  , isMonoid
  , isMonotoneComposition
  , isGaloisConnection
  , Prop3, Property3, Property4
    -- * Generators
  , natural
  , positive
  , maybeGen
  , maybeCoGen
  , listOfElements
  , elementsUnlessEmpty
  , two
  , three
    -- * Tasty framework functions
  , testGroup
  , testProperties
  , testProperty
  , TestTree
    -- * Test driver.
  , runTests
  )
  where

import Control.Monad

import qualified Control.Monad.Fail as Fail

import Data.Functor
import Data.Monoid ( mappend, mempty, Monoid )
import Data.Semigroup ( (<>), Semigroup )
import Test.QuickCheck
import Test.Tasty ( testGroup, TestName, TestTree )
import Test.Tasty.QuickCheck ( testProperties, testProperty )

import Agda.Utils.PartialOrd
import Agda.Utils.POMonoid

------------------------------------------------------------------------
-- QuickCheck helpers

#if !MIN_VERSION_QuickCheck(2,12,5)
isSuccess :: Result -> Bool
isSuccess Success{} = True
isSuccess _         = False
#endif

quickCheck' :: Testable prop => prop -> IO Bool
quickCheck' p = fmap isSuccess $ quickCheckResult p

quickCheckWith' :: Testable prop => Args -> prop -> IO Bool
quickCheckWith' args p = fmap isSuccess $ quickCheckWithResult args p

------------------------------------------------------------------------
-- Algebraic properties

-- | Is the operator associative?

isAssociative :: Eq a
              => (a -> a -> a)
              -> a -> a -> a -> Bool
isAssociative (+) = \x y z ->
  x + (y + z) == (x + y) + z

-- | Is the operator commutative?

isCommutative :: Eq a
              => (a -> a -> a)
              -> a -> a -> Bool
isCommutative (+) = \x y ->
  x + y == y + x

-- | Is the operator idempotent?

isIdempotent :: Eq a
             => (a -> a -> a)
             -> a -> Bool
isIdempotent (/\) = \ x ->
  (x /\ x) == x

-- | Is the element a zero for the operator?

isZero :: Eq a
       => a -> (a -> a -> a)
       -> a -> Bool
isZero zer (*) = \x ->
  (zer * x == zer)
  &&
  (x * zer == zer)

-- | Is the element a unit for the operator?

isIdentity :: Eq a
           => a -> (a -> a -> a)
           -> a -> Bool
isIdentity one (*) = \x ->
  (one * x == x)
  &&
  (x * one == x)

-- | Does the first operator distribute (from the left) over the
-- second one?

isLeftDistributive
  :: Eq a
  => (a -> a -> a) -> (a -> a -> a)
  -> a -> a -> a -> Bool
isLeftDistributive (*) (+) = \x y z ->
  x * (y + z) == (x * y) + (x * z)

-- | Does the first operator distribute (from the right) over the
-- second one?

isRightDistributive
  :: Eq a
  => (a -> a -> a) -> (a -> a -> a)
  -> a -> a -> a -> Bool
isRightDistributive (*) (+) = \x y z ->
  (x + y) * z == (x * z) + (y * z)

-- | Does the first operator distribute over the second one?

isDistributive
  :: Eq a
  => (a -> a -> a) -> (a -> a -> a)
  -> a -> a -> a -> Bool
isDistributive (*) (+) = \ x y z ->
  isLeftDistributive (*) (+) x y z &&
  isRightDistributive (*) (+) x y z

-- | Property over 3 variables.

type Prop3     a = a -> a -> a -> Bool
type Property3 a = a -> a -> a -> Property

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

type Property4 a = a -> a -> a -> a -> Property

-- | Is the semigroup operation monotone in both arguments
--   wrt. to the associated partial ordering?

isMonotoneComposition :: (Eq a, POSemigroup a) => Property4 a
isMonotoneComposition x x' y y' =
  related x POLE x' && related y POLE y' ==> related (x <> y) POLE (x' <> y')

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

------------------------------------------------------------------------
-- Instances

instance Fail.MonadFail Gen where
  fail = error

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
