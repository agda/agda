module Agda.TypeChecking.Constraints where

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Constraints (MonadConstraint)
import Agda.TypeChecking.Warnings (MonadWarning)

import Agda.Utils.Except (MonadError)

instance MonadConstraint TCM where

solveAwakeConstraints' :: MonadConstraint m => Bool -> m ()
noConstraints          :: (MonadConstraint m, MonadWarning m, MonadError TCErr m, MonadFresh ProblemId m)
                       => m a -> m a
ifNoConstraints_       :: TCM () -> TCM a -> (ProblemId -> TCM a) -> TCM a
ifNoConstraints        :: TCM a -> (a -> TCM b) -> (ProblemId -> a -> TCM b) -> TCM b
guardConstraint        :: Constraint -> TCM () -> TCM ()
debugConstraints       :: TCM ()
