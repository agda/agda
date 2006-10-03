-- | Termination checker, based on
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch.
--
-- TODO: Note that we should also check that data type definitions are
-- strictly positive. Furthermore, for inductive-recursive families we
-- may need to do something more clever.

module Termination.Termination
  ( terminates
  ) where

import Termination.Lexicographic
import Termination.Utilities
import Termination.CallGraph
import Termination.Matrix
import Control.Arrow
import Test.QuickCheck
import qualified Data.Set as Set
import qualified Data.Array as Array

-- | @'terminates' cs@ returns 'Nothing' if the algorithm in the paper
-- referred to above can detect that the functions represented by @cs@
-- terminate. Otherwise it returns a list of functions ('Index'es)
-- which it cannot see are terminating.
--
-- The call graph @cs@ should have one entry ('Call') per recursive
-- function application.
--
-- Note that this function assumes that all data types are strictly
-- positive.
--
-- Preconditions: @'completePrecondition' cs@.
--
-- Note that it is possible to return a lexicographic ordering
-- verifying the termination of the functions. Note also that, with
-- extra work, better error messages can be given (something like
-- \"the i-th function is not properly decreasing in its j-th, k-th or
-- m-th arguments\").

terminates :: CallGraph -> Maybe [Index]
terminates cs
  | all ((/=) Nothing . snd) lexs = Nothing
  | otherwise = Just $ map fst $ filter ((==) Nothing . snd) $ lexs
  where
  -- Complete the call graph.
  ccs = complete cs
  -- Compute the "recursion behaviours".
  rbs = [ (source c, Array.elems $ diagonal (mat (cm c)))
        | c <- Set.toList ccs, source c == target c ]
  -- Group them by function name.
  rbs' = map (fst . head &&& map snd) $ groupOn fst rbs
  -- Try to find lexicographic orders.
  lexs = [ (i, lexOrder rb) | (i, rb) <- rbs' ]

-- | The example from the paper.

example :: CallGraph
example = Set.fromList [c1, c2, c3]
  where
  flat = 0
  aux  = 1
  c1 = Call { source = flat, target = aux
            , cm = CallMatrix $ fromLists (Size 2 1) [[Lt], [Lt]] }
  c2 = Call { source = aux,  target = aux
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Lt, Unknown]
                                                     , [Unknown, Le]] }
  c3 = Call { source = aux,  target = flat
            , cm = CallMatrix $ fromLists (Size 1 2) [[Unknown, Le]] }

prop_terminates = terminates example == Nothing

------------------------------------------------------------------------
-- All tests

tests = do
  quickCheck prop_terminates
