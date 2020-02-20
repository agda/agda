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
  , endos
  , idempotent
  ) where

import Agda.Termination.CutOff
import Agda.Termination.CallGraph
import Agda.Termination.CallMatrix hiding (toList)
import qualified Agda.Termination.CallMatrix as CMSet
import Agda.Termination.Order
import Agda.Termination.SparseMatrix

import Agda.Utils.Maybe



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
checkIdems calls = caseMaybe (listToMaybe offending) (Right ()) $ Left . augCallInfo
  where
    -- Every idempotent call must have decrease, otherwise it offends us.
    offending = filter (not . hasDecrease) $ filter idempotent calls

-- UNUSED Liang-Ting 2019-07-15
--checkIdem :: (?cutoff :: CutOff) => CallMatrixAug cinfo -> Bool
--checkIdem c = if idempotent c then hasDecrease c else True

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
