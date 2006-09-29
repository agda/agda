-- | Some algebraic properties, phrased as boolean functions.

module Termination.TestHelpers
  ( associative
  , commutative
  , zero
  , identity
  , leftDistributive
  , rightDistributive
  , semiring
  )
  where

import Test.QuickCheck

associative :: (Arbitrary a, Eq a, Show a)
            => (a -> a -> a)
            -> a -> a -> a -> Bool
associative (+) = \x y z ->
  x + (y + z) == (x + y) + z

commutative :: (Arbitrary a, Eq a, Show a)
            => (a -> a -> a)
            -> a -> a -> Bool
commutative (+) = \x y ->
  x + y == y + x

zero :: (Arbitrary a, Eq a, Show a)
     => a -> (a -> a -> a)
     -> a -> Bool
zero zer (*) = \x ->
  (zer * x == zer)
  &&
  (x * zer == zer)

identity :: (Arbitrary a, Eq a, Show a)
         => a -> (a -> a -> a)
         -> a -> Bool
identity one (*) = \x ->
  (one * x == x)
  &&
  (x * one == x)

leftDistributive
  :: (Arbitrary a, Eq a, Show a)
  => (a -> a -> a) -> (a -> a -> a)
  -> a -> a -> a -> Bool
leftDistributive (*) (+) = \x y z ->
  x * (y + z) == (x * y) + (x * z)

rightDistributive
  :: (Arbitrary a, Eq a, Show a)
  => (a -> a -> a) -> (a -> a -> a)
  -> a -> a -> a -> Bool
rightDistributive (*) (+) = \x y z ->
  (x + y) * z == (x * z) + (y * z)

-- I think it's OK to use the same x, y, z triple for all the
-- properties below.

semiring :: (Arbitrary a, Eq a, Show a)
         => (a -> a -> a) -> (a -> a -> a) -> a -> a
         -> a -> a -> a -> Bool
semiring (+) (*) zer one = \x y z ->
  associative (+)           x y z &&
  identity zer (+)          x     &&
  commutative (+)           x y   &&
  associative (*)           x y z &&
  identity one (*)          x     &&
  leftDistributive (*) (+)  x y z &&
  rightDistributive (*) (+) x y z &&
  zero zer (*)              x
