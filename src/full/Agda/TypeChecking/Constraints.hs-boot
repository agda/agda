module Agda.TypeChecking.Constraints where

import Agda.TypeChecking.Monad.Base

addConstraint          :: Constraint -> TCM ()
catchConstraint        :: Constraint -> TCM () -> TCM ()
solveConstraint        :: Constraint -> TCM ()
solveAwakeConstraints' :: Bool -> TCM ()
noConstraints          :: TCM a -> TCM a
ifNoConstraints_       :: TCM () -> TCM a -> (ProblemId -> TCM a) -> TCM a
guardConstraint        :: Constraint -> TCM () -> TCM ()
debugConstraints       :: TCM ()
