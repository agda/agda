
module Agda.TypeChecking.Irrelevance where

import Agda.Syntax.Internal (LensSort)

import Agda.TypeChecking.Monad.Base (MonadTCEnv, HasOptions, MonadReduce)
import Agda.TypeChecking.Monad.Debug (MonadDebug)
import {-# SOURCE #-} Agda.TypeChecking.Pretty (PrettyTCM)

workOnTypes :: (MonadTCEnv m, HasOptions m, MonadDebug m) => m a -> m a
isPropM :: (LensSort a, PrettyTCM a, MonadReduce m, MonadDebug m) => a -> m Bool
