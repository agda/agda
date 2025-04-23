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
  , endos
  , idempotent
  ) where

import Prelude hiding ((&&), null)

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

terminates :: (Monoid cinfo, ?cutoff :: CutOff) => CallGraph cinfo -> Terminates cinfo
terminates = terminatesFilter $ const True

terminatesFilter ::
     (Monoid cinfo, ?cutoff :: CutOff)
  => (Node -> Bool)    -- ^ Only consider calls whose source and target satisfy this predicate.
  -> CallGraph cinfo   -- ^ Callgraph augmented with @cinfo@.
  -> Terminates cinfo  -- ^ A bad call path of type @cinfo@, if termination could not be proven.
terminatesFilter f cs
  | cm:_ <- bad             = TerminatesNot GuardednessHelpsNot $ augCallInfo cm
  | cm:_ <- needGuardedness = TerminatesNot GuardednessHelpsYes $ augCallInfo cm
  | otherwise               = Terminates
  where
    f' = f . source && f . target
    -- Every idempotent call must have decrease in the diagonal.
    idems = filter idempotent $ endos $ filter f' $ toList $ complete cs
    hasDecr cm = case diagonal cm of
      g : xs
        | any isDecr xs -> In1 ()        -- Evidence found without guardedness.
        | isDecr g      -> In2 cm        -- Evidence found in guardedness.
        | otherwise     -> In3 cm        -- No evidence found.
      []                -> In3 cm        -- No information means no evidence for termination.
    (good, needGuardedness, bad) = partitionEithers3 $ map hasDecr idems

endos :: [Call cinfo] -> [CallMatrixAug cinfo]
endos cs = [ m | c <- cs, source c == target c
               , m <- CMSet.toList $ callMatrixSet c
           ]

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
