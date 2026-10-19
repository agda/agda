{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Constraints where

import Agda.Syntax.Internal (ProblemId)
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Constraints (MonadConstraint)
import Agda.TypeChecking.Warnings (MonadWarning)

instance MonadConstraint TCM where

noConstraints          :: (MonadConstraint m, MonadWarning m, MonadFresh ProblemId m)
                       => m a -> m a
ifNoConstraints_       :: TCM () -> TCM a -> (ProblemId -> TCM a) -> TCM a
ifNoConstraints        :: TCM a -> (a -> TCM b) -> (ProblemId -> a -> TCM b) -> TCM b
guardConstraint        :: Constraint -> TCM () -> TCM ()
debugConstraints       :: TCM ()
