
module Agda.TypeChecking.Irrelevance where

import Agda.TypeChecking.Monad.Base (MonadTCEnv, HasOptions)
import Agda.TypeChecking.Monad.Debug (MonadDebug)

workOnTypes :: (MonadTCEnv m, HasOptions m, MonadDebug m) => m a -> m a
