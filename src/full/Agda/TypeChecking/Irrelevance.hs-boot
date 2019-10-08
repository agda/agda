
module Agda.TypeChecking.Irrelevance where

import Agda.Syntax.Internal (LensSort)

import Agda.TypeChecking.Monad.Base (MonadTCEnv, HasOptions, MonadReduce)
import Agda.TypeChecking.Monad.Debug (MonadDebug)

workOnTypes :: (MonadTCEnv m, HasOptions m, MonadDebug m) => m a -> m a
isPropM :: (LensSort a, MonadReduce m) => a -> m Bool
