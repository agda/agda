module Agda.TypeChecking.Constraints where

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Constraints (MonadConstraint)

instance MonadConstraint TCM where

solveAwakeConstraints' :: MonadConstraint m => Bool -> m ()
noConstraints          :: TCM a -> TCM a
ifNoConstraints_       :: TCM () -> TCM a -> (ProblemId -> TCM a) -> TCM a
ifNoConstraints        :: TCM a -> (a -> TCM b) -> (ProblemId -> a -> TCM b) -> TCM b
guardConstraint        :: Constraint -> TCM () -> TCM ()
debugConstraints       :: TCM ()
