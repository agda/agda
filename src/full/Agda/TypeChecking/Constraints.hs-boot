module Agda.TypeChecking.Constraints where

import Agda.TypeChecking.Monad.Base

addConstraint          :: Constraint -> TCM ()
solveAwakeConstraints' :: Bool -> TCM ()
noConstraints          :: TCM a -> TCM a
ifNoConstraints_       :: TCM () -> TCM a -> (ProblemId -> TCM a) -> TCM a
