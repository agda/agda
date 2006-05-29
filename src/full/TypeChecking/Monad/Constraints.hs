
module TypeChecking.Monad.Constraints where

import Control.Monad.State
import Data.Map as Map

import TypeChecking.Monad.Base
import TypeChecking.Monad.Signature
import TypeChecking.Monad.Context

-- | Get the constraints
getConstraints :: TCM Constraints
getConstraints = gets stConstraints

lookupConstraint :: ConstraintId -> TCM ConstraintClosure
lookupConstraint i =
    do	cs <- getConstraints
	case Map.lookup i cs of
	    Just c  -> return c
	    _	    -> fail $ "no such constraint: " ++ show i

-- | Take constraints (clear all constraints).
takeConstraints :: TCM Constraints
takeConstraints =
    do	cs <- getConstraints
	modify $ \s -> s { stConstraints = Map.empty }
	return cs

withConstraint :: (Constraint -> TCM a) -> ConstraintClosure -> TCM a
withConstraint f (CC sig env c) =
    withSignature sig
    $ withEnv env
    $ f c

