-- | Some functions and generators suitable for writing QuickCheck
-- properties.

module InternalTests.Helpers
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
    -- * Generators
  , natural
  , positive
  , maybeGen
  , maybeCoGen
  , listOfElements
  , elementsUnlessEmpty
  , two
  , three
    -- * Test driver.
  , runTests
  )
  where

import Control.Monad
import Data.Functor
import Data.Semigroup ( (<>), mappend, mempty, Monoid, Semigroup )
import Test.QuickCheck

------------------------------------------------------------------------
-- QuickCheck helpers

isSuccess :: Result -> Bool
isSuccess Success{} = True
isSuccess _         = False

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

-- | Does the operator satisfy the semigroup law?

isSemigroup :: (Eq a, Semigroup a) => a -> a -> a -> Bool
isSemigroup = isAssociative (<>)

-- | Does the operator satisfy the monoid laws?

isMonoid :: (Eq a, Semigroup a, Monoid a) => a -> a -> a -> Bool
isMonoid x y z =
-- ASR (2017-01-25): What if `mappend ≠ (<>)`? It isn't possible
-- because we are using the `-Wnoncanonical-monoid-instances` flag.
  isSemigroup x y z &&
  isIdentity mempty mappend x

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
-- Test driver

-- | Runs the tests, and returns 'True' if all tests were successful.

runTests :: String    -- ^ A label for the tests. Used for
                      --   informational purposes.
         -> [IO Bool]
         -> IO Bool
runTests name tests = do
  putStrLn name
  and <$> sequence tests
