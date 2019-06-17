
module Agda.TypeChecking.Monad.MetaVars where

import Control.Monad.Reader
import Control.Monad.State

import Agda.Syntax.Common (InteractionId)
import Agda.TypeChecking.Monad.Base

class (MonadTCEnv m, ReadTCState m) => MonadInteractionPoints m where
  freshInteractionId :: m InteractionId
  modifyInteractionPoints :: (InteractionPoints -> InteractionPoints) -> m ()

instance MonadInteractionPoints m => MonadInteractionPoints (ReaderT r m)
instance MonadInteractionPoints m => MonadInteractionPoints (StateT r m)

instance MonadInteractionPoints TCM
