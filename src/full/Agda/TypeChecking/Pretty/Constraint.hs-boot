{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Pretty.Constraint where

import Agda.Syntax.Common.Pretty (Doc)
import Agda.TypeChecking.Pretty (MonadPretty, PrettyTCM)
import Agda.TypeChecking.Monad.Base (ProblemConstraint)

prettyInterestingConstraints :: MonadPretty m => [ProblemConstraint] -> m [Doc]
interestingConstraint        :: MonadPretty m => ProblemConstraint -> m Bool

instance PrettyTCM ProblemConstraint
