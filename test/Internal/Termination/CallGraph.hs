{-# LANGUAGE ImplicitParams #-}

module Internal.Termination.CallGraph ( tests ) where

import Agda.Termination.CallGraph
import Agda.Termination.CutOff
import Agda.Termination.SparseMatrix

import qualified Data.List as List

import Internal.Helpers
import Internal.Termination.CallMatrix ( callMatrix )

------------------------------------------------------------------------------

-- prop_complete :: (?cutoff :: CutOff) => Property
-- prop_complete =
--   forAll (callGraph :: Gen (CallGraph [Integer])) $ \cs ->
--     isComplete (complete cs)

-- -- | Returns 'True' iff the call graph is complete.

-- isComplete :: (Ord cinfo, Monoid cinfo, ?cutoff :: CutOff) => CallGraph cinfo -> Bool
-- isComplete s = (s `union` (s `combine` s)) `notWorse` s

------------------------------------------------------------------------
-- * Generators and properties
------------------------------------------------------------------------

-- | Generates a call graph.

callGraph :: Arbitrary cinfo => Gen (CallGraph cinfo)
callGraph = do
  indices <- fmap List.nub arbitrary
  n <- natural
  let noMatrices | List.null indices = 0
                 | otherwise    = n `min` 3  -- Not too many.
  fromList <$> vectorOf noMatrices (matGen indices)
  where
  matGen indices = do
    [s, t] <- vectorOf 2 (elements indices)
    [c, r] <- vectorOf 2 (choose (0, 2))     -- Not too large.
    m <- callMatrix (Size { rows = r, cols = c })
    mkCall s t m <$> arbitrary

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
