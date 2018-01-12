{-# LANGUAGE ImplicitParams #-}

module Internal.Termination.Termination ( tests ) where

import Agda.Termination.CutOff
import Agda.Termination.CallGraph
import Agda.Termination.CallMatrix -- hiding (toList)
import Agda.Termination.Order
import Agda.Termination.SparseMatrix
import Agda.Termination.Termination

import Agda.Utils.Either

import Internal.Helpers -- hiding (idempotent)

------------------------------------------------------------------------
-- Some examples

{- Convention (see TermCheck):
   Guardedness flag is in position (0,0) of the matrix,
   it is always present even if the functions are all recursive.
   The examples below do not include the guardedness flag, though.
 -}

-- | The call graph instantiation used by the examples below.

type CG = CallGraph ()

-- | Constructs a call graph.  No meta info.

buildCallGraph :: [Call ()] -> CG
buildCallGraph = fromList

-- | The example from the JFP'02 paper.

example1 :: CG
example1 = buildCallGraph [c1, c2, c3]
  where
  flat = 1
  aux  = 2
  c1 = mkCall' flat aux $ CallMatrix $ fromLists (Size 2 1) [ [lt]
                                                            , [lt]]
  c2 = mkCall' aux  aux $ CallMatrix $ fromLists (Size 2 2) [ [lt, unknown]
                                                            , [unknown, le]]
  c3 = mkCall' aux flat $ CallMatrix $ fromLists (Size 1 2) [ [unknown, le]]

prop_terminates_example1 ::  (?cutoff :: CutOff) => Bool
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
  c = mkCall' plus plus $ CallMatrix $ fromLists (Size 2 2) [ [unknown, le]
                                                            , [lt, unknown] ]

prop_terminates_example2 ::  (?cutoff :: CutOff) => Bool
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
  c f g = mkCall' f g $ CallMatrix $ fromLists (Size 2 2) [ [unknown, le]
                                                         , [lt, unknown] ]

prop_terminates_example3 ::  (?cutoff :: CutOff) => Bool
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
  c1 = mkCall' f f $ CallMatrix $ fromLists (Size 2 2) $
         [ [le, unknown]
         , [unknown, le] ]

  c2 = mkCall' f g $ CallMatrix $ fromLists (Size 2 2) $
         [ [lt, unknown]
         , [unknown, le] ]

  c3 = mkCall' g f $ CallMatrix $ fromLists (Size 2 2) $
         [ [le, unknown]
         , [unknown, le] ]

prop_terminates_example4 ::  (?cutoff :: CutOff) => Bool
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
  c1 = mkCall' f g $ CallMatrix $ fromLists (Size 2 2) [ [lt, unknown]
                                                       , [unknown, le] ]
  c2 = mkCall' f f $ CallMatrix $ fromLists (Size 2 2) [ [unknown, unknown]
                                                       , [unknown, lt] ]
  c3 = mkCall' g f $ CallMatrix $ fromLists (Size 2 2) [ [le, unknown]
                                                       , [unknown, le] ]
  c4 = mkCall' g g $ CallMatrix $ fromLists (Size 2 2) [ [lt, unknown]
                                                       , [unknown, le] ]

prop_terminates_example5 ::  (?cutoff :: CutOff) => Bool
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
  c1 = mkCall' f f $ CallMatrix $ fromLists (Size 1 1) [ [lt] ]
  c2 = mkCall' f f $ CallMatrix $ fromLists (Size 1 1) [ [le] ]
  c3 = mkCall' f f $ CallMatrix $ fromLists (Size 1 1) [ [le] ]

prop_terminates_example6 ::  (?cutoff :: CutOff) => Bool
prop_terminates_example6 = isLeft $ terminates example6

-- See issue 1055.
-- (The following function was adapted from Lee, Jones, and Ben-Amram,
-- POPL '01).
--
-- p : ℕ → ℕ → ℕ → ℕ
-- p m n        (succ r) = p m r n
-- p m (succ n) zero     = p zero n m
-- p m zero     zero     = m

example7 :: CG
example7 = buildCallGraph [call1, call2]
  where
    call1 = mkCall' 1 1 $ CallMatrix $ fromLists (Size 3 3)
      [ [le, le, le]
      , [un, lt, un]
      , [le, un, un]
      ]
    call2 = mkCall' 1 1 $ CallMatrix $ fromLists (Size 3 3)
      [ [le, un, un]
      , [un, un, lt]
      , [un, le, un]
      ]
    un = unknown

prop_terminates_example7 ::  (?cutoff :: CutOff) => Bool
prop_terminates_example7 = isRight $ terminates example7

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- (ASR 2018-01-06) Since some properties use implicit parameters we
-- cannot use 'allProperties' for collecting all the tests (see
-- https://github.com/nick8325/quickcheck/issues/193 ).

tests :: TestTree
tests = testGroup "Internal.Termination.Termination"
  [ testProperty "prop_terminates_example1" prop_terminates_example1
  , testProperty "prop_terminates_example2" prop_terminates_example2
  , testProperty "prop_terminates_example3" prop_terminates_example3
  , testProperty "prop_terminates_example4" prop_terminates_example4
  , testProperty "prop_terminates_example5" prop_terminates_example5
  , testProperty "prop_terminates_example6" prop_terminates_example6
  , testProperty "prop_terminates_example7" prop_terminates_example7
  ]
  where ?cutoff = CutOff 0 -- all these examples are with just lt,le,unknown
