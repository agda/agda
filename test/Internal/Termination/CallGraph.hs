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
-- All tests

-- (ASR 2017-12-25) Since some properties use implicit parameters we
-- could not use 'quickCheckAll' for collecting all the tests (see
-- https://github.com/nick8325/quickcheck/issues/193 ).

tests :: IO Bool
tests = runTests "Internal.Termination.CallGraph" []
  -- [ quickCheck' prop_complete
  -- , quickCheck' prop_ensureCompletePrecondition
  -- ]
  where ?cutoff = DontCutOff -- CutOff 2  -- don't cut off in tests!
