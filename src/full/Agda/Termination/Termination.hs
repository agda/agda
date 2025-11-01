{-# OPTIONS_GHC -Wunused-imports #-}

{-# LANGUAGE ImplicitParams #-}

-- | Termination checker, based on
--     \"A Predicative Analysis of Structural Recursion\" by
--     Andreas Abel and Thorsten Altenkirch (JFP'01),
--   and
--     \"The Size-Change Principle for Program Termination\" by
--     Chin Soon Lee, Neil Jones, and Amir Ben-Amram (POPL'01).

module Agda.Termination.Termination
  ( Terminates(..)
  , GuardednessHelps(..)
  , terminates
  , terminatesFilter
  , terminationCounterexample
  , idempotentEndos
  ) where

import Prelude hiding ((&&), not, null)

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

import Agda.Termination.CutOff
import Agda.Termination.CallGraph
import Agda.Termination.CallMatrix hiding (toList)
import qualified Agda.Termination.CallMatrix as CMSet
import Agda.Termination.Order
import Agda.Termination.SparseMatrix

import Agda.Utils.Boolean
import Agda.Utils.Null
import Agda.Utils.Three

-- | Would termination go through with guardedness?
data GuardednessHelps
  = GuardednessHelpsYes  -- ^ Guardedness would provide termination evidence.
  | GuardednessHelpsNot  -- ^ Guardedness does not help with termination.
  deriving (Eq, Show, Generic, Enum, Bounded)

-- | Result of running the termination checker.
data Terminates cinfo
  = Terminates
      -- ^ Termination proved without considering guardedness.
  | TerminatesNot GuardednessHelps cinfo
      -- ^ Termination could not be proven,
      --   witnessed by the supplied problematic call path.
      --   Guardedness could help, though.


-- | @'terminates' cs@ checks if the functions represented by @cs@
-- terminate. The call graph @cs@ should have one entry ('Call') per
-- recursive function application.
--
-- The termination criterion is taken from Jones et al.
-- In the completed call graph, each idempotent call-matrix
-- from a function to itself must have a decreasing argument.
-- Idempotency is wrt. matrix multiplication.
--
-- This criterion is strictly more liberal than searching for a
-- lexicographic order (and easier to implement, but harder to justify).
--
-- 'terminates' does not use guardedness, 'terminatesFilter' is more general.
terminates :: (Monoid cinfo, ?cutoff :: CutOff) => CallGraph cinfo -> Terminates cinfo
terminates = terminatesFilter False $ const True

-- | While no counterexample to termination is found,
--   complete the given call graph step-by-step.
terminatesFilter :: forall cinfo. (Monoid cinfo, ?cutoff :: CutOff)
  => Bool              -- ^ Use guardedness?
  -> (Node -> Bool)    -- ^ Only consider calls whose source and target satisfy this predicate.
  -> CallGraph cinfo   -- ^ Callgraph augmented with @cinfo@.
  -> Terminates cinfo  -- ^ A bad call path of type @cinfo@, if termination could not be proven.
terminatesFilter useGuardedness f cs0 = loop (cs0, cs0)
  where
    loop :: (CallGraph cinfo, CallGraph cinfo) -> Terminates cinfo
    loop (new, cs)
      -- If we have no new calls, the call graph is complete,
      -- and we have not found a counterexample.
      | null new  = Terminates
      -- Otherwise the new calls might contain a counterexample.
      | otherwise = case terminationCounterexample useGuardedness f new of
          -- If we have a counterexample already, we can stop the search for one.
          result@TerminatesNot{} -> result
          -- Otherwise, we continue to complete the call-graph one step and look again.
          Terminates -> loop $ completionStep cs0 cs

-- | Does the given callgraph contain a counterexample to termination?
terminationCounterexample :: (Monoid cinfo, ?cutoff :: CutOff)
  => Bool              -- ^ Use guardedness?
  -> (Node -> Bool)    -- ^ Only consider calls whose source and target satisfy this predicate.
  -> CallGraph cinfo   -- ^ Callgraph augmented with @cinfo@.
  -> Terminates cinfo  -- ^ A bad call path of type @cinfo@, if termination could not be proven.
terminationCounterexample useGuardedness f cs
  | cm:_ <- bad             = TerminatesNot GuardednessHelpsNot $ augCallInfo cm
  | cm:_ <- needGuardedness
  , not useGuardedness      = TerminatesNot GuardednessHelpsYes $ augCallInfo cm
  | otherwise               = Terminates
  where
    -- Every idempotent call must have decrease in the diagonal.
    (_good, needGuardedness, bad) = partitionEithers3 $ map hasDecr idems
    idems = idempotentEndosFilter f cs
    hasDecr cm = case diagonal cm of
      g : xs
        | any isDecr xs -> In1 ()        -- Evidence found without guardedness.
        | isDecr g      -> In2 cm        -- Evidence found in guardedness.
        | otherwise     -> In3 cm        -- No evidence found.
      []                -> In3 cm        -- No information means no evidence for termination.

-- | Get all idempotent call-matrixes of loops in the call graph that match the given node-filter.
idempotentEndosFilter :: (?cutoff :: CutOff) => (Node -> Bool) -> CallGraph cinfo -> [CallMatrixAug cinfo]
idempotentEndosFilter f = filter idempotent . concatMap (CMSet.toList . snd) . filter (f . fst) . loops

-- | Get all idempotent call-matrixes of loops in the call graph.
idempotentEndos :: (?cutoff :: CutOff) => CallGraph cinfo -> [CallMatrixAug cinfo]
idempotentEndos = idempotentEndosFilter $ const True

-- | A call @c@ is idempotent if it is an endo (@'source' == 'target'@)
--   of order 1.
--   (Endo-calls of higher orders are e.g. argument permutations).
--   We can test idempotency by self-composition.
--   Self-composition @c >*< c@ should not make any parameter-argument relation
--   worse.
idempotent  :: (?cutoff :: CutOff) => CallMatrixAug cinfo -> Bool
idempotent (CallMatrixAug m _) = (m >*< m) `notWorse` m

-- Instances

instance Null GuardednessHelps where
  empty = GuardednessHelpsNot

instance Boolean GuardednessHelps where
  fromBool = \case
    True  -> GuardednessHelpsYes
    False -> GuardednessHelpsNot

instance IsBool GuardednessHelps where
  toBool = \case
    GuardednessHelpsYes -> True
    GuardednessHelpsNot -> False

instance NFData GuardednessHelps
