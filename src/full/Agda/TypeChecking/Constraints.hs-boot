module Agda.TypeChecking.Constraints where

import Agda.TypeChecking.Monad.Base

addConstraint :: Constraint -> TCM ()
solveAwakeConstraints' :: Bool -> TCM ()
