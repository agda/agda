{-# LANGUAGE CPP            #-}
{-# LANGUAGE ImplicitParams #-}

#if __GLASGOW_HASKELL__ >= 800
{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
#endif

-- | Termination checker, based on
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch (JFP'01),
--   and
--     \"The Size-Change Principle for Program Termination\" by
--     Chin Soon Lee, Neil Jones, and Amir Ben-Amram (POPL'01).

module Agda.Termination.Termination
  ( terminates
  , terminatesFilter
  , endos
  , idempotent
  , Agda.Termination.Termination.tests
  ) where

import Agda.Termination.CutOff
import Agda.Termination.CallGraph  hiding (tests)
import Agda.Termination.CallMatrix hiding (tests, toList)
import qualified Agda.Termination.CallMatrix as CMSet
import Agda.Termination.Order      hiding (tests)
import Agda.Termination.SparseMatrix

import Agda.Utils.Either
import Agda.Utils.List
import Agda.Utils.Maybe
import Agda.Utils.TestHelpers hiding (idempotent)
import Agda.Utils.QuickCheck

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

terminates :: (Monoid cinfo, ?cutoff :: CutOff) => CallGraph cinfo -> Either cinfo ()
terminates cs = checkIdems $ endos $ toList $ complete cs

terminatesFilter :: (Monoid cinfo, ?cutoff :: CutOff) =>
  (Node -> Bool) -> CallGraph cinfo -> Either cinfo ()
terminatesFilter f cs = checkIdems $ endos $ filter f' $ toList $ complete cs
  where f' c = f (source c) && f (target c)

endos :: [Call cinfo] -> [CallMatrixAug cinfo]
endos cs = [ m | c <- cs, source c == target c
               , m <- CMSet.toList $ callMatrixSet c
           ]

checkIdems :: (?cutoff :: CutOff) => [CallMatrixAug cinfo] -> Either cinfo ()
checkIdems calls = caseMaybe (headMaybe offending) (Right ()) $ Left . augCallInfo
  where
    -- Every idempotent call must have decrease, otherwise it offends us.
    offending = filter (not . hasDecrease) $ filter idempotent calls

checkIdem :: (?cutoff :: CutOff) => CallMatrixAug cinfo -> Bool
checkIdem c = if idempotent c then hasDecrease c else True

-- | A call @c@ is idempotent if it is an endo (@'source' == 'target'@)
--   of order 1.
--   (Endo-calls of higher orders are e.g. argument permutations).
--   We can test idempotency by self-composition.
--   Self-composition @c >*< c@ should not make any parameter-argument relation
--   worse.
idempotent  :: (?cutoff :: CutOff) => CallMatrixAug cinfo -> Bool
idempotent (CallMatrixAug m _) = (m >*< m) `notWorse` m

hasDecrease :: CallMatrixAug cinfo -> Bool
hasDecrease = any isDecr . diagonal

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
-- All tests

tests :: IO Bool
tests = runTests "Agda.Termination.Termination"
  [ quickCheck' prop_terminates_example1
  , quickCheck' prop_terminates_example2
  , quickCheck' prop_terminates_example3
  , quickCheck' prop_terminates_example4
  , quickCheck' prop_terminates_example5
  , quickCheck' prop_terminates_example6
  , quickCheck' prop_terminates_example7
  ]
  where ?cutoff = CutOff 0 -- all these examples are with just lt,le,unknown
