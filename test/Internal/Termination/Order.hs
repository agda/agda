{-# LANGUAGE ImplicitParams #-}

module Internal.Termination.Order ( tests ) where

import Agda.Termination.CutOff
import Agda.Termination.Order

import Internal.Helpers
import qualified Internal.Termination.Semiring as Semiring

------------------------------------------------------------------------------

{- instances cannot have implicit arguments?! GHC manual says:

7.8.3.1. Implicit-parameter type constraints

You can't have an implicit parameter in the context of a class or instance declaration. For example, both these declarations are illegal:

  class (?x::Int) => C a where ...
  instance (?x::a) => Foo [a] where ...

Reason: exactly which implicit parameter you pick up depends on
exactly where you invoke a function. But the ``invocation'' of
instance declarations is done behind the scenes by the compiler, so
it's hard to figure out exactly where it is done. Easiest thing is to
outlaw the offending types.

instance (?cutoff :: CutOff) => Arbitrary Order where
  arbitrary = frequency
    [(20, return Unknown)
    ,(80, elements [- ?cutoff .. ?cutoff + 1] >>= Decr)
    ] -- no embedded matrices generated for now.
-}
instance Arbitrary Order where
  arbitrary = frequency
    [(30, return Unknown)
    ,(70, elements [0,1] >>= return . Decr True)
    ] -- no embedded matrices generated for now.

instance CoArbitrary Order where
  coarbitrary (Decr _ k) = variant 0
  coarbitrary Unknown  = variant 1
  coarbitrary (Mat m)  = variant 2

------------------------------------------------------------------------------

prop_decr :: (?cutoff :: CutOff) => Bool -> Int -> Bool
prop_decr u = isOrder . decr u

prop_orderSemiring :: (?cutoff :: CutOff) => Order -> Order -> Order -> Bool
prop_orderSemiring = Semiring.semiringInvariant orderSemiring

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- (ASR 2018-01-06) Since some properties use implicit parameters we
-- cannot use 'allProperties' for collecting all the tests (see
-- https://github.com/nick8325/quickcheck/issues/193 ).

tests :: TestTree
tests = testGroup "Internal.Termination.Order"
  [ testProperty "prop_decr" prop_decr
  , testProperty "prop_orderSemiring" prop_orderSemiring
  ]
  where ?cutoff = DontCutOff -- CutOff 2  -- don't cut off in tests!
