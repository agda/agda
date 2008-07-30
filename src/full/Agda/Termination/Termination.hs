-- | Termination checker, based on
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch (JFP'01).
--   and
--     \"The Size-Change Principle for Program Termination\" by
--     Chin Soon Lee, Neil Jones, and Amir Ben-Amram (POPL'01).
--
-- TODO: Note that we should also check that data type definitions are
-- strictly positive. Furthermore, for inductive-recursive families we
-- may need to do something more clever.

module Agda.Termination.Termination
  ( terminates
  , Agda.Termination.Termination.tests
  ) where

import Agda.Termination.Lexicographic
import Agda.Termination.Utilities
import Agda.Termination.CallGraph
import Agda.Termination.Matrix
import Agda.Utils.Either
import Agda.Utils.TestHelpers
import Control.Arrow
import Test.QuickCheck
import qualified Data.Set as Set
import qualified Data.Array as Array
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid
import Data.Array (Array)

-- | TODO: This comment seems to be partly out of date.
--
-- @'terminates' cs@ checks if the functions represented by @cs@
-- terminate. The call graph @cs@ should have one entry ('Call') per
-- recursive function application.
--
-- @'Right' perms@ is returned if the functions are size-change terminating.
--
-- If termination can not be established, then @'Left' problems@ is
-- returned instead. Here @problems@ contains an
-- indication of why termination cannot be established. See 'lexOrder'
-- for further details.
--
-- Note that this function assumes that all data types are strictly
-- positive.
--
-- The termination criterion is taken from Jones et al.
-- In the completed call graph, each idempotent call-matrix 
-- from a function to itself must have a decreasing argument.
-- Idempotency is wrt. matrix multiplication.
--
-- This criterion is strictly more liberal than searching for a 
-- lexicographic order (and easier to implement, but harder to justify).

terminates :: (Ord meta, Monoid meta) => CallGraph meta -> Either meta ()
terminates cs = let ccs = complete cs
                in
                  checkIdems $ toList ccs

checkIdems :: (Ord meta,Monoid meta) => [(Call,meta)] -> Either meta ()
checkIdems [] = Right ()
checkIdems ((c,m):xs) = if (checkIdem c) then checkIdems xs else Left m

checkIdem :: Call -> Bool
checkIdem c = let b = target c == source c
                  idem = (c >*< c) == c
                  hasDecr = any isDecr $ Array.elems $ diagonal (mat (cm c))
                  in
                    (not b) || (not idem) || hasDecr

-- | Matrix is decreasing if any diagonal element is 'Lt'.

isDecr :: Order -> Bool
isDecr Lt = True
isDecr (Mat m) = any isDecr $ Array.elems $ diagonal m
isDecr _ = False

------------------------------------------------------------------------
-- Some examples

-- | The call graph instantiation used by the examples below.

type CG = CallGraph (Set Integer)

-- | Constructs a call graph suitable for use with the 'R' monoid.

buildCallGraph :: [Call] -> CG
buildCallGraph = fromList . flip zip (map Set.singleton [1 ..])

-- | The example from the JFP'02 paper.

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

prop_terminates_example1 = isRight $ terminates example1

-- | An example which is now handled by this algorithm: argument
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

prop_terminates_example2 = isRight $ terminates example2 

-- | A related example which is anyway handled: argument swapping addition
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

prop_terminates_example3 = isRight $ terminates example3 

-- | A contrived example.
--
-- @f (S x) y = f (S x) y + g x y@
--
-- @f Z     y = y@
--
-- @g x y = f x y@
--
-- TODO: This example checks that the meta information is reported properly
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

prop_terminates_example4 = isLeft $ terminates example4

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

prop_terminates_example5 = isRight $ terminates example5 

-- | Another example which should fail.
--
-- @f (S x) = f x + f (S x)@
--
-- @f x     = f x@
--
-- TODO: This example checks that the meta information is reported properly
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

prop_terminates_example6 = isLeft $ terminates example6 

------------------------------------------------------------------------
-- All tests

tests = runTests "Agda.Termination.Termination"
  [ quickCheck' prop_terminates_example1
  , quickCheck' prop_terminates_example2
  , quickCheck' prop_terminates_example3
  , quickCheck' prop_terminates_example4
  , quickCheck' prop_terminates_example5
  , quickCheck' prop_terminates_example6
  ]
