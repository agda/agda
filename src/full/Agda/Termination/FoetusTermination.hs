{-# OPTIONS_GHC -Wunused-imports #-}

-- RETIRED

-- | Termination checker, based on
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch.
--
-- TODO: Note that we should also check that data type definitions are
-- strictly positive. Furthermore, for inductive-recursive families we
-- may need to do something more clever.

module Agda.Termination.FoetusTermination
  ( terminates
  , recursionBehaviours
  , Agda.Termination.Termination.tests
  ) where

import Control.Arrow

import Data.Monoid
import Data.Array (Array)
import qualified Data.Array as Array
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Termination.Lexicographic
import Agda.Termination.CallGraph
import Agda.Termination.CallMatrix
import Agda.Termination.Order
import Agda.Termination.Matrix

import Agda.Utils.QuickCheck
import Agda.Utils.Tuple

import Agda.Utils.Impossible

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

terminates :: (Ord cinfo, Monoid cinfo) =>
  CallGraph cinfo -> Either (Map Index (Set Index, Set cinfo))
                            (Map Index (LexOrder Index))
terminates cs | ok        = Right perms
              | otherwise = Left problems
  where
  -- Try to find lexicographic orders.
  lexs = [ (i, lexOrder $ fromDiagonals rb)
         | (i, rb) <- recursionBehaviours cs ]

  ok       = Map.null problems
  perms    = Map.fromListWith __IMPOSSIBLE__ [ (x, y)             | (x, Right y) <- lexs ]
  problems = Map.fromListWith __IMPOSSIBLE__ [ (x, Set.map snd y) | (x, Left  y) <- lexs ]

-- | Completes the call graph and computes the corresponding recursion
-- behaviours.
--
-- Takes the same kind of input as 'terminates'.
--
-- For every function ('Index') a bunch of arrays is returned. Every
-- array states one way in which the function calls itself (perhaps
-- via other functions); one call path. The merged meta information
-- associated with all the calls in such a call path is paired up with
-- the array. It may be that several different call paths give rise to
-- the same array. In that case the array is returned once; the pieces
-- of meta information associated to the different call paths are
-- merged using 'mappend'.

recursionBehaviours :: (Ord cinfo, Monoid cinfo) =>
     CallGraph cinfo -> [(Index, [(cinfo, Array Index Order)])]
recursionBehaviours cs = rbs'
  where
  -- Complete the call graph.
  ccs = complete cs
  -- Compute the "recursion behaviours" (matrix diagonals).
  rbs = [ (source c, (callIds, diagonal (mat (cm c))))
        | (c, callIds) <- toList ccs, source c == target c ]
  -- Group them by function name.
  rbs' = map (fst . head &&& map snd) $ groupOn fst rbs

------------------------------------------------------------------------
-- Some examples

-- | The call graph instantiation used by the examples below.

type CG = CallGraph (Set Integer)

-- | Constructs a call graph suitable for use with the 'R' monoid.

buildCallGraph :: [Call] -> CG
buildCallGraph = fromList . flip zip (map Set.singleton [1 ..])

-- | The example from the paper.

example1 :: CG
example1 = buildCallGraph [c1, c2, c3]
  where
  flat = 1
  aux  = 2
  c1 = Call { source = flat, target = aux
            , cm = CallMatrix $ fromLists (Size 2 1) [[Lt], [Lt]] }
  c2 = Call { source = aux,  target = aux
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Lt, Unknown]
                                                     , [Unknown, Le]] }
  c3 = Call { source = aux,  target = flat
            , cm = CallMatrix $ fromLists (Size 1 2) [[Unknown, Le]] }

prop_terminates_example1 =
  terminates example1 == Right (Map.fromListWith __IMPOSSIBLE__ [(1, [1]), (2, [2, 1])])

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
  c = Call { source = plus, target = plus
           , cm = CallMatrix $ fromLists (Size 2 2) [ [Unknown, Le]
                                                    , [Lt, Unknown] ] }

prop_terminates_example2 =
  terminates example2 ==
  Left (Map.singleton 1 ( Set.fromList [1, 2]
                        , Set.fromList [Set.fromList [1]] ))

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
example3 = buildCallGraph [c plus plus', c plus' plus]
  where
  plus  = 1
  plus' = 2
  c f g = Call { source = f, target = g
               , cm = CallMatrix $ fromLists (Size 2 2) [ [Unknown, Le]
                                                        , [Lt, Unknown] ] }

prop_terminates_example3 =
  terminates example3 == Right (Map.fromListWith __IMPOSSIBLE__ [(1, [1]), (2, [1])])

-- | A contrived example.
--
-- @f (S x) y = f (S x) y + g x y@
--
-- @f Z     y = y@
--
-- @g x y = f x y@
--
-- This example checks that the meta information is reported properly
-- when an error is encountered.

example4 :: CG
example4 = buildCallGraph [c1, c2, c3]
  where
  f = 1
  g = 2
  c1 = Call { source = f, target = f
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Le, Unknown]
                                                     , [Unknown, Le] ] }
  c2 = Call { source = f, target = g
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Lt, Unknown]
                                                     , [Unknown, Le] ] }
  c3 = Call { source = g, target = f
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Le, Unknown]
                                                     , [Unknown, Le] ] }

prop_terminates_example4 =
  terminates example4 ==
  Left (Map.singleton 1 ( Set.fromList [2]
                        , Set.fromList [Set.fromList [1]] ))

-- | This should terminate.
--
-- @f (S x) (S y) = g x (S y) + f (S (S x)) y@
--
-- @g (S x) (S y) = f (S x) (S y) + g x (S y)@

example5 :: CG
example5 = buildCallGraph [c1, c2, c3, c4]
  where
  f = 1
  g = 2
  c1 = Call { source = f, target = g
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Lt, Unknown]
                                                     , [Unknown, Le] ] }
  c2 = Call { source = f, target = f
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Unknown, Unknown]
                                                     , [Unknown, Lt] ] }
  c3 = Call { source = g, target = f
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Le, Unknown]
                                                     , [Unknown, Le] ] }
  c4 = Call { source = g, target = g
            , cm = CallMatrix $ fromLists (Size 2 2) [ [Lt, Unknown]
                                                     , [Unknown, Le] ] }

prop_terminates_example5 =
  terminates example5 == Right (Map.fromListWith __IMPOSSIBLE__ [(1, [2, 1]), (2, [2, 1])])

-- | Another example which should fail.
--
-- @f (S x) = f x + f (S x)@
--
-- @f x     = f x@
--
-- This example checks that the meta information is reported properly
-- when an error is encountered.

example6 :: CG
example6 = buildCallGraph [c1, c2, c3]
  where
  f = 1
  c1 = Call { source = f, target = f
            , cm = CallMatrix $ fromLists (Size 1 1) [ [Lt] ] }
  c2 = Call { source = f, target = f
            , cm = CallMatrix $ fromLists (Size 1 1) [ [Le] ] }
  c3 = Call { source = f, target = f
            , cm = CallMatrix $ fromLists (Size 1 1) [ [Le] ] }

prop_terminates_example6 =
  terminates example6 ==
  Left (Map.singleton 1 ( Set.fromList []
                        , Set.fromList [Set.fromList [2, 3]] ))

------------------------------------------------------------------------
-- All tests

tests = do
  quickCheck prop_terminates_example1
  quickCheck prop_terminates_example2
  quickCheck prop_terminates_example3
  quickCheck prop_terminates_example4
  quickCheck prop_terminates_example5
  quickCheck prop_terminates_example6
