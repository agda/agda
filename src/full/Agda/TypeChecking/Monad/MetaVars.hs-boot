
module Agda.TypeChecking.Monad.MetaVars where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Identity ( IdentityT )

import Agda.Syntax.Common (InteractionId, MetaId)
import Agda.TypeChecking.Monad.Base

class (MonadTCEnv m, ReadTCState m) => MonadInteractionPoints m where
  freshInteractionId :: m InteractionId
  modifyInteractionPoints :: (InteractionPoints -> InteractionPoints) -> m ()

  default freshInteractionId
    :: (MonadTrans t, MonadInteractionPoints n, t n ~ m)
    => m InteractionId
  freshInteractionId = lift freshInteractionId

  default modifyInteractionPoints
    :: (MonadTrans t, MonadInteractionPoints n, t n ~ m)
    => (InteractionPoints -> InteractionPoints) -> m ()
  modifyInteractionPoints = lift . modifyInteractionPoints

instance MonadInteractionPoints m => MonadInteractionPoints (IdentityT m)
instance MonadInteractionPoints m => MonadInteractionPoints (ReaderT r m)
instance MonadInteractionPoints m => MonadInteractionPoints (StateT s m)

instance MonadInteractionPoints TCM

isInteractionMeta :: ReadTCState m => MetaId -> m (Maybe InteractionId)
