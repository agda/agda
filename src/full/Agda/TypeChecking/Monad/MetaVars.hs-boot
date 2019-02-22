
module Agda.TypeChecking.Monad.MetaVars where

import Agda.Syntax.Common (InteractionId)
import Agda.TypeChecking.Monad.Base

class (MonadTCEnv m, ReadTCState m) => MonadInteractionPoints m where
  freshInteractionId :: m InteractionId
  modifyInteractionPoints :: (InteractionPoints -> InteractionPoints) -> m ()

instance MonadInteractionPoints TCM
