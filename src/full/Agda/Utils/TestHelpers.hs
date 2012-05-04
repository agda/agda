-- | Some functions and generators suitable for writing QuickCheck
-- properties.

module Agda.Utils.TestHelpers
  ( -- * Algebraic properties
    associative
  , commutative
  , isZero
  , identity
  , leftDistributive
  , rightDistributive
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
import Data.List

import Agda.Utils.QuickCheck

------------------------------------------------------------------------
-- Algebraic properties

-- | Is the operator associative?

associative :: (Arbitrary a, Eq a, Show a)
            => (a -> a -> a)
            -> a -> a -> a -> Bool
associative (+) = \x y z ->
  x + (y + z) == (x + y) + z

-- | Is the operator commutative?

commutative :: (Arbitrary a, Eq a, Show a)
            => (a -> a -> a)
            -> a -> a -> Bool
commutative (+) = \x y ->
  x + y == y + x

-- | Is the element a zero for the operator?

isZero :: (Arbitrary a, Eq a, Show a)
     => a -> (a -> a -> a)
     -> a -> Bool
isZero zer (*) = \x ->
  (zer * x == zer)
  &&
  (x * zer == zer)

-- | Is the element a unit for the operator?

identity :: (Arbitrary a, Eq a, Show a)
         => a -> (a -> a -> a)
         -> a -> Bool
identity one (*) = \x ->
  (one * x == x)
  &&
  (x * one == x)

-- | Does the first operator distribute (from the left) over the
-- second one?

leftDistributive
  :: (Arbitrary a, Eq a, Show a)
  => (a -> a -> a) -> (a -> a -> a)
  -> a -> a -> a -> Bool
leftDistributive (*) (+) = \x y z ->
  x * (y + z) == (x * y) + (x * z)

-- | Does the first operator distribute (from the right) over the
-- second one?

rightDistributive
  :: (Arbitrary a, Eq a, Show a)
  => (a -> a -> a) -> (a -> a -> a)
  -> a -> a -> a -> Bool
rightDistributive (*) (+) = \x y z ->
  (x + y) * z == (x * z) + (y * z)

------------------------------------------------------------------------
-- Generators

-- | Generates natural numbers.

natural :: (Integral i) => Gen i
natural = fmap (fromInteger . abs) arbitrary

-- | Generates positive numbers.

positive :: (Integral i) => Gen i
positive = fmap ((+ 1) . abs . fromInteger) arbitrary

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
                         , (9, fmap Just gen)
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
  fmap and $ sequence tests
