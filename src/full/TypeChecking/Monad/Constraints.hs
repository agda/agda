
module TypeChecking.Monad.Constraints where

import Control.Monad.State
import Data.Map as Map

import TypeChecking.Monad.Base
import TypeChecking.Monad.Signature
import TypeChecking.Monad.Env
import TypeChecking.Monad.State
import TypeChecking.Monad.Closure

-- | Get the constraints
getConstraints :: TCM Constraints
getConstraints = gets stConstraints

lookupConstraint :: Int -> TCM ConstraintClosure
lookupConstraint i =
    do	cs <- getConstraints
	unless (i < length cs) $ fail $ "no such constraint: " ++ show i
	return $ cs !! i

-- | Take constraints (clear all constraints).
takeConstraints :: TCM Constraints
takeConstraints =
    do	cs <- getConstraints
	modify $ \s -> s { stConstraints = [] }
	return cs

withConstraint :: (Constraint -> TCM a) -> ConstraintClosure -> TCM a
withConstraint = flip enterClosure

-- | Add new constraints
addConstraints :: Constraints -> TCM ()
addConstraints cs = modify $ \st -> st { stConstraints = cs ++ stConstraints st }

-- | Create a new constraint.
buildConstraint :: Constraint -> TCM Constraints
buildConstraint c = do
    cl <- buildClosure c
    return [cl]

