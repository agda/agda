
module Agda.TypeChecking.Monad.Constraints where

import Control.Monad.State
import Control.Monad.Reader
import Data.Map as Map
import Data.List as List

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Signature
import Agda.TypeChecking.Monad.Env
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Closure

-- | Get the awake constraints
getAwakeConstraints :: MonadTCM tcm => tcm Constraints
getAwakeConstraints = gets stAwakeConstraints

wakeConstraints :: MonadTCM tcm => (ConstraintClosure -> Bool) -> tcm ()
wakeConstraints wake = modify $ \s ->
  let (wakeup, sleepin) = List.partition wake (stSleepingConstraints s) in
  s { stSleepingConstraints = sleepin
    , stAwakeConstraints    = stAwakeConstraints s ++ wakeup
    }

takeAwakeConstraint :: MonadTCM tcm => tcm (Maybe ConstraintClosure)
takeAwakeConstraint = do
  cs <- getAwakeConstraints
  case cs of
    []     -> return Nothing
    c : cs -> do
      modify $ \s -> s { stAwakeConstraints = cs }
      return (Just c)

getAllConstraints :: MonadTCM tcm => tcm Constraints
getAllConstraints = gets $ \s -> stAwakeConstraints s ++ stSleepingConstraints s

withConstraint :: MonadTCM tcm => (Constraint -> tcm a) -> ConstraintClosure -> tcm a
withConstraint = flip enterClosure

-- | Add new constraints
addConstraints' :: MonadTCM tcm => Constraints -> tcm ()
addConstraints' cs = modify $ \st -> st { stSleepingConstraints = cs ++ stSleepingConstraints st }

-- | Add already awake constraints
addAwakeConstraints :: MonadTCM tcm => Constraints -> tcm ()
addAwakeConstraints cs = modify $ \s -> s { stAwakeConstraints = cs ++ stAwakeConstraints s }

-- | Start solving constraints
nowSolvingConstraints :: MonadTCM tcm => tcm a -> tcm a
nowSolvingConstraints = local $ \e -> e { envSolvingConstraints = True }

isSolvingConstraints :: MonadTCM tcm => tcm Bool
isSolvingConstraints = asks envSolvingConstraints

-- | Create a new constraint.
buildConstraint :: MonadTCM tcm => Constraint -> tcm Constraints
buildConstraint = liftM return . buildConstraint'

buildConstraint' :: MonadTCM tcm => Constraint -> tcm ConstraintClosure
buildConstraint' c = do
    cl <- buildClosure c
    return cl
