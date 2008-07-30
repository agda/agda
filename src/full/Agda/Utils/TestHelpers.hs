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
    -- * Other tests
  , allEqual
    -- * Generators
  , natural
  , positive
  , maybeGen
  , maybeCoGen
  , listOfElements
    -- * Test driver.
  , runTests
  )
  where

import Test.QuickCheck
import Data.List

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
-- Other tests

-- | Checks if all the elements in the list are equal. Assumes that
-- the 'Eq' instance stands for an equivalence relation.

allEqual :: Eq a => [a] -> Bool
allEqual []       = True
allEqual (x : xs) = all (== x) xs

------------------------------------------------------------------------
-- Generators

-- | Generates natural numbers.

natural :: (Arbitrary i, Integral i) => Gen i
natural = fmap abs arbitrary

-- | Generates positive numbers.

positive :: (Arbitrary i, Integral i) => Gen i
positive = fmap ((+ 1) . abs) arbitrary

-- | Generates a list of elements picked from a given list.
listOfElements :: [a] -> Gen [a]
listOfElements [] = return []
listOfElements xs = listOf $ elements xs

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
