
module Agda.TypeChecking.Monad.Constraints where

import Control.Monad.State
import Data.Map as Map

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Closure

-- | Get the constraints
getConstraints :: MonadTCM tcm => tcm Constraints
getConstraints = gets stConstraints

lookupConstraint :: MonadTCM tcm => Int -> tcm ConstraintClosure
lookupConstraint i =
    do	cs <- getConstraints
	unless (i < length cs) $ fail $ "no such constraint: " ++ show i
	return $ cs !! i

-- | Take constraints (clear all constraints).
takeConstraints :: MonadTCM tcm => tcm Constraints
takeConstraints =
    do	cs <- getConstraints
	modify $ \s -> s { stConstraints = [] }
	return cs

withConstraint :: MonadTCM tcm => (Constraint -> tcm a) -> ConstraintClosure -> tcm a
withConstraint = flip enterClosure

-- | Add new constraints
addConstraints :: MonadTCM tcm => Constraints -> tcm ()
addConstraints cs = modify $ \st -> st { stConstraints = cs ++ stConstraints st }

-- | Create a new constraint.
buildConstraint :: MonadTCM tcm => Constraint -> tcm Constraints
buildConstraint c = do
    cl <- buildClosure c
    return [cl]

