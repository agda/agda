{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Pretty.Constraint where

import Text.PrettyPrint (Doc)
import Agda.TypeChecking.Pretty (MonadPretty, PrettyTCM)
import Agda.TypeChecking.Monad.Base (ProblemConstraint)

prettyInterestingConstraints :: MonadPretty m => [ProblemConstraint] -> m [Doc]
interestingConstraint        :: ProblemConstraint -> Bool

instance PrettyTCM ProblemConstraint
