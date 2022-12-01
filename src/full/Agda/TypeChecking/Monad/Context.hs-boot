
module Agda.TypeChecking.Monad.Context where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Control  ( MonadTransControl(..), liftThrough )
import Control.Monad.Trans.Identity ( IdentityT )

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base

checkpointSubstitution :: MonadTCEnv tcm => CheckpointId -> tcm Substitution

class MonadTCEnv m => MonadAddContext m where
  addCtx :: Name -> Dom Type -> m a -> m a
  addLetBinding' :: Origin -> Name -> Term -> Dom Type -> m a -> m a
  updateContext :: Substitution -> (Context -> Context) -> m a -> m a
  withFreshName :: Range -> ArgName -> (Name -> m a) -> m a

  default addCtx
    :: (MonadAddContext n, MonadTransControl t, t n ~ m)
    => Name -> Dom Type -> m a -> m a
  addCtx x a = liftThrough $ addCtx x a

  default addLetBinding'
    :: (MonadAddContext n, MonadTransControl t, t n ~ m)
    => Origin -> Name -> Term -> Dom Type -> m a -> m a
  addLetBinding' o x u a = liftThrough $ addLetBinding' o x u a

  default updateContext
    :: (MonadAddContext n, MonadTransControl t, t n ~ m)
    => Substitution -> (Context -> Context) -> m a -> m a
  updateContext sub f = liftThrough $ updateContext sub f

  default withFreshName
    :: (MonadAddContext n, MonadTransControl t, t n ~ m)
    => Range -> ArgName -> (Name -> m a) -> m a
  withFreshName r x cont = do
    st <- liftWith $ \ run -> do
      withFreshName r x $ run . cont
    restoreT $ return st

instance MonadAddContext m => MonadAddContext (IdentityT m) where
instance MonadAddContext m => MonadAddContext (ReaderT r m) where
instance MonadAddContext m => MonadAddContext (StateT r m) where

instance MonadAddContext TCM
