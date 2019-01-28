{-# LANGUAGE ImplicitParams #-}

module Internal.Termination.CallGraph ( tests ) where

import Agda.Termination.CutOff

import Internal.Helpers

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- (ASR 2018-01-06) Since some properties use implicit parameters we
-- cannot use 'allProperties' for collecting all the tests (see
-- https://github.com/nick8325/quickcheck/issues/193 ).

tests :: TestTree
tests = testGroup "Internal.Termination.CallGraph" []
  -- [ testProperty "prop_complete" prop_complete
  -- , testProperty "prop_ensureCompletePrecondition"
  -- ]
  where ?cutoff = DontCutOff -- CutOff 2  -- don't cut off in tests!
