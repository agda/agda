-- | Termination checker, based on
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch.
--
-- TODO: Note that we should also check that data type definitions are
-- strictly positive. Furthermore, for inductive-recursive families we
-- may need to do something more clever.

module Termination.Termination
  ( terminates
  , Termination.Termination.tests
  ) where

import Termination.Lexicographic
import Termination.Utilities
import Termination.CallGraph
import Termination.Matrix
import Control.Arrow
import Test.QuickCheck
import qualified Data.Set as Set
import qualified Data.Array as Array
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid

-- | @'terminates' cs@ checks if the functions represented by @cs@
-- terminate. The call graph @cs@ should have one entry ('Call') per
-- recursive function application.
--
-- @'Right' perms@ is returned if the algorithm in the paper referred
-- to above can detect that the functions terminate. Here @perms@
-- contains one permutation (lexicographic ordering) for every
-- function; these permutations witness the termination of the
-- functions. (For more details, see the paper and 'lexOrder'.)
--
-- If termination can not be established, then @'Left' problems@ is
-- returned instead. Here @problems@ contains, for every function, an
-- indication of why termination cannot be established. See 'lexOrder'
-- for further details.
--
-- Note that this function assumes that all data types are strictly
-- positive.

terminates :: (Ord call, Monoid call) =>
  CallGraph call -> Either (Map Index (Set Index, Set call))
                           (Map Index (LexOrder Index))
terminates cs | ok        = Right perms 
              | otherwise = Left problems
  where
  -- Complete the call graph.
  ccs = complete cs
  -- Compute the "recursion behaviours" (matrix diagonals).
  rbs = [ (source c, (callId c, diagonal (mat (cm c))))
        | c <- toList ccs, source c == target c ]
  -- Group them by function name.
  rbs' = map (fst . head &&& map snd) $ groupOn fst rbs
  -- Try to find lexicographic orders.
  lexs = [ (i, lexOrder $ fromDiagonals rb) | (i, rb) <- rbs' ]

  ok = all (isRight . snd) lexs
  perms = Map.fromList $
          map (id *** (\(Right x) -> x)) $ filter (isRight . snd) lexs
  problems = Map.fromList $
             map (id *** (\(Left x) -> (id *** Set.map snd) x)) $
             filter (isLeft . snd) lexs

------------------------------------------------------------------------
-- Some examples

-- First some infrastructure.

-- | The monoid instance for @'R' a@ always chooses the
-- right (second) value, if it is defined.

data R a = RNothing | RJust a
  deriving (Show, Eq, Ord)

instance Monoid (R a) where
  mempty        = RNothing
  l@(RJust {}) `mappend` RNothing = l
  _            `mappend` r        = r

-- | The call graph instantiation used by the examples below.

type CG = CallGraph (R Integer)

-- | Constructs a call graph suitable for use with the 'R' monoid.

buildCallGraph :: [Call Integer] -> CG
buildCallGraph = fromList . map (\c -> c { callId = RJust $ callId c })

-- | Constructs result lists suitable for use with the 'R' monoid.

buildResults :: Ord a
             => Either (Map Index (Set Index, Set a))     b
             -> Either (Map Index (Set Index, Set (R a))) b
buildResults =
 (Map.fromList .
  map (id *** (id *** Set.fromList . map RJust . Set.toList)) .
  Map.toList)
 +++
 id

-- | The example from the paper.

example1 :: CG
example1 = buildCallGraph [c1, c2, c3]
  where
  flat = 1
  aux  = 2
  c1 = Call { source = flat, target = aux, callId = 1
            , cm = CallMatrix $ fromLists (Size 2 1) [[Lt], [Lt]] }
  c2 = Call { source = aux,  target = aux, callId = 2
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Lt, Unknown]
                                                     , [Unknown, Le]] }
  c3 = Call { source = aux,  target = flat, callId = 3
            , cm = CallMatrix $ fromLists (Size 1 2) [[Unknown, Le]] }

prop_terminates_example1 =
  terminates example1 ==
  buildResults (Right (Map.fromList [(1, [1]), (2, [2, 1])]))

-- | An example which is not handled by this algorithm: argument
-- swapping addition.
--
-- @S x + y = S (y + x)@
--
-- @Z   + y = y@

example2 :: CG
example2 = buildCallGraph [c]
  where
  plus = 1
  c = Call { source = plus, target = plus, callId = 1
           , cm = CallMatrix $ fromLists (Size 2 2) [ [Unknown, Le]
                                                    , [Lt, Unknown] ] }

prop_terminates_example2 =
  terminates example2 ==
  buildResults (Left (Map.fromList [(1, ( Set.fromList [1, 2]
                                        , Set.fromList [1]))]))

-- | A related example which /is/ handled: argument swapping addition
-- using two alternating functions.
--
-- @S x + y = S (y +' x)@
--
-- @Z   + y = y@
--
-- @S x +' y = S (y + x)@
--
-- @Z   +' y = y@

example3 :: CG
example3 = buildCallGraph [c plus plus' 1, c plus' plus 2]
  where
  plus  = 1
  plus' = 2
  c f g id = Call { source = f, target = g, callId = id
                  , cm = CallMatrix $ fromLists (Size 2 2) [ [Unknown, Le]
                                                           , [Lt, Unknown] ] }

prop_terminates_example3 =
  terminates example3 ==
  buildResults (Right (Map.fromList [(1, [1]), (2, [1])]))

-- | A final, contrived example.
--
-- @f (S x) y = f (S x) y + g x y@
--
-- @f Z     y = y@
--
-- @g x y = f x y@
--
-- This example checks that 'callId's are reported properly.

example4 :: CG
example4 = buildCallGraph [c1, c2, c3]
  where
  f = 1
  g = 2
  c1 = Call { source = f, target = f, callId = 1
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Le, Unknown]
                                                     , [Unknown, Le] ] }
  c2 = Call { source = f, target = g, callId = 2
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Lt, Unknown]
                                                     , [Unknown, Le] ] }
  c3 = Call { source = g, target = f, callId = 3
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Le, Unknown]
                                                     , [Unknown, Le] ] }

prop_terminates_example4 =
  terminates example4 ==
  buildResults (Left (Map.fromList [(1, ( Set.fromList [2]
                                        , Set.fromList [1]))]))

-- | This should terminate.  2007-05-29
--
--  @f (succ x) (succ y) = (g x (succ y)) + (f  (succ (succ x)) y)@ 
--
--  @g (succ x) (succ y) = (f (succ x) (succ y)) + (g x (succ y))@
--

example5 :: CG
example5 = buildCallGraph [c1, c2, c3, c4]
  where
  f = 1
  g = 2
  c1 = Call { source = f, target = g, callId = 1
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Lt, Unknown]
                                                     , [Unknown, Le] ] }
  c2 = Call { source = f, target = f, callId = 2
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Unknown, Unknown]
                                                     , [Unknown, Lt] ] }
  c3 = Call { source = g, target = f, callId = 3
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Le, Unknown]
                                                     , [Unknown, Le] ] }
  c4 = Call { source = g, target = g, callId = 4
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Lt, Unknown]
                                                     , [Unknown, Le] ] }

prop_terminates_example5 = isRight (terminates example5)

------------------------------------------------------------------------
-- All tests

tests = do
  quickCheck prop_terminates_example1
  quickCheck prop_terminates_example2
  quickCheck prop_terminates_example3
  quickCheck prop_terminates_example4
  quickCheck prop_terminates_example5
