{-# LANGUAGE ImplicitParams #-}

-- | Termination checker, based on
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch (JFP'01),
--   and
--     \"The Size-Change Principle for Program Termination\" by
--     Chin Soon Lee, Neil Jones, and Amir Ben-Amram (POPL'01).

module Agda.Termination.Termination
  ( terminates
  , terminatesFilter
  , Agda.Termination.Termination.tests
  ) where

import Agda.Termination.Lexicographic
import Agda.Termination.CallGraph
import Agda.Termination.SparseMatrix

import Agda.Utils.Either
import Agda.Utils.TestHelpers
import Agda.Utils.QuickCheck

import Control.Arrow

import Data.Array (Array)
import qualified Data.Array as Array
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Monoid

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

terminates :: (Ord meta, Monoid meta, ?cutoff :: Int) => CallGraph meta -> Either meta ()
terminates cs = let ccs = complete cs
                in
                  checkIdems $ toList ccs

terminatesFilter :: (Ord meta, Monoid meta, ?cutoff :: Int) =>
  (Index -> Bool) -> CallGraph meta -> Either meta ()
terminatesFilter f cs = checkIdems $ filter f' $ toList $ complete cs
  where f' (c,m) = f (source c) && f (target c)

checkIdems :: (Ord meta, Monoid meta, ?cutoff :: Int) => [(Call,meta)] -> Either meta ()
checkIdems [] = Right ()
checkIdems ((c,m):xs) = if (checkIdem c) then checkIdems xs else Left m

{- Convention (see TermCheck):
   Guardedness flag is in position (0,0) of the matrix,
   it is always present even if the functions are all recursive.
   The examples below do not include the guardedness flag, though.
 -}

checkIdem :: (?cutoff :: Int) => Call -> Bool
checkIdem c = let
  b = target c == source c
  idem = (c >*< c) == c
  diag =  Array.elems $ diagonal (mat (cm c))
  hasDecr = any isDecr $ diag
  in
    (not b) || (not idem) || hasDecr

-- | Matrix is decreasing if any diagonal element is decreasing.

isDecr :: Order -> Bool
isDecr (Mat m) = any isDecr $ Array.elems $ diagonal m
isDecr o = decreasing o

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
            , cm = CallMatrix $ fromLists (Size 2 1) [[lt], [lt]]
            }
  c2 = Call { source = aux,  target = aux
            , cm = CallMatrix $ fromLists (Size 2 2) [ [lt, unknown]
                                                     , [unknown, le]]
            }
  c3 = Call { source = aux,  target = flat
            , cm = CallMatrix $ fromLists (Size 1 2) [[unknown, le]]
            }

prop_terminates_example1 ::  (?cutoff :: Int) => Bool
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
           , cm = CallMatrix $ fromLists (Size 2 2) [ [unknown, le]
                                                    , [lt, unknown] ]
           }

prop_terminates_example2 ::  (?cutoff :: Int) => Bool
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
               , cm = CallMatrix $ fromLists (Size 2 2) [ [unknown, le]
                                                        , [lt, unknown] ]
               }

prop_terminates_example3 ::  (?cutoff :: Int) => Bool
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
            , cm = CallMatrix $ fromLists (Size 2 2) [ [le, unknown]
                                                     , [unknown, le] ]
            }
  c2 = Call { source = f, target = g
            , cm = CallMatrix $ fromLists (Size 2 2) [ [lt, unknown]
                                                     , [unknown, le] ]
            }
  c3 = Call { source = g, target = f
            , cm = CallMatrix $ fromLists (Size 2 2) [ [le, unknown]
                                                     , [unknown, le] ]
            }

prop_terminates_example4 ::  (?cutoff :: Int) => Bool
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
            , cm = CallMatrix $ fromLists (Size 2 2) [ [lt, unknown]
                                                     , [unknown, le] ]
            }
  c2 = Call { source = f, target = f
            , cm = CallMatrix $ fromLists (Size 2 2) [ [unknown, unknown]
                                                     , [unknown, lt] ]
            }
  c3 = Call { source = g, target = f
            , cm = CallMatrix $ fromLists (Size 2 2) [ [le, unknown]
                                                     , [unknown, le] ]
            }
  c4 = Call { source = g, target = g
            , cm = CallMatrix $ fromLists (Size 2 2) [ [lt, unknown]
                                                     , [unknown, le] ]
            }

prop_terminates_example5 ::  (?cutoff :: Int) => Bool
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
            , cm = CallMatrix $ fromLists (Size 1 1) [ [lt] ]
            }
  c2 = Call { source = f, target = f
            , cm = CallMatrix $ fromLists (Size 1 1) [ [le] ]
            }
  c3 = Call { source = f, target = f
            , cm = CallMatrix $ fromLists (Size 1 1) [ [le] ]
            }

prop_terminates_example6 ::  (?cutoff :: Int) => Bool
prop_terminates_example6 = isLeft $ terminates example6

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Termination.Termination"
  [ quickCheck' prop_terminates_example1
  , quickCheck' prop_terminates_example2
  , quickCheck' prop_terminates_example3
  , quickCheck' prop_terminates_example4
  , quickCheck' prop_terminates_example5
  , quickCheck' prop_terminates_example6
  ]
  where ?cutoff = 0 -- all these examples are with just lt,le,unknown
