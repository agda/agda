-- | Some functions and generators suitable for writing QuickCheck
-- properties.

module Agda.Utils.TestHelpers
  ( -- * Algebraic properties
    associative
  , commutative
  , idempotent
  , isZero
  , identity
  , leftDistributive
  , rightDistributive
  , distributive
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
import Test.QuickCheck

------------------------------------------------------------------------
-- Algebraic properties

-- | Is the operator associative?

associative :: Eq a
            => (a -> a -> a)
            -> a -> a -> a -> Bool
associative (+) = \x y z ->
  x + (y + z) == (x + y) + z

-- | Is the operator commutative?

commutative :: Eq a
            => (a -> a -> a)
            -> a -> a -> Bool
commutative (+) = \x y ->
  x + y == y + x

-- | Is the operator idempotent?

idempotent :: Eq a
            => (a -> a -> a)
            -> a -> Bool
idempotent (/\) = \ x ->
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

identity :: Eq a
         => a -> (a -> a -> a)
         -> a -> Bool
identity one (*) = \x ->
  (one * x == x)
  &&
  (x * one == x)

-- | Does the first operator distribute (from the left) over the
-- second one?

leftDistributive
  :: Eq a
  => (a -> a -> a) -> (a -> a -> a)
  -> a -> a -> a -> Bool
leftDistributive (*) (+) = \x y z ->
  x * (y + z) == (x * y) + (x * z)

-- | Does the first operator distribute (from the right) over the
-- second one?

rightDistributive
  :: Eq a
  => (a -> a -> a) -> (a -> a -> a)
  -> a -> a -> a -> Bool
rightDistributive (*) (+) = \x y z ->
  (x + y) * z == (x * z) + (y * z)

-- | Does the first operator distribute over the second one?

distributive
  :: Eq a
  => (a -> a -> a) -> (a -> a -> a)
  -> a -> a -> a -> Bool
distributive (*) (+) = \ x y z ->
  leftDistributive (*) (+) x y z &&
  rightDistributive (*) (+) x y z

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
