{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Monad.Context where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Control  ( MonadTransControl(..), liftThrough )
import Control.Monad.Trans.Identity ( IdentityT )

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import Agda.Utils.CallStack (HasCallStack)

checkpointSubstitution :: MonadTCEnv tcm => CheckpointId -> tcm Substitution

class MonadTCEnv m => MonadAddContext m where
  addCtx :: HasCallStack => Name -> Dom Type -> m a -> m a
  addLetBinding' :: IsAxiom -> Origin -> Name -> Term -> Dom Type -> m a -> m a
  addLocalRewrite :: RewriteRule -> m a -> m a
  updateContext' :: RefreshRews -> Substitution -> (Context -> Context) -> m a -> m a
  withFreshName :: Range -> ArgName -> (Name -> m a) -> m a

  default addCtx
    :: (MonadAddContext n, MonadTransControl t, t n ~ m, HasCallStack)
    => Name -> Dom Type -> m a -> m a
  addCtx x a = liftThrough $ addCtx x a

  default addLetBinding'
    :: (MonadAddContext n, MonadTransControl t, t n ~ m)
    => IsAxiom -> Origin -> Name -> Term -> Dom Type -> m a -> m a
  addLetBinding' o x u a = liftThrough $ addLetBinding' o x u a

  default addLocalRewrite
    :: (MonadAddContext n, MonadTransControl t, t n ~ m)
    => RewriteRule -> m a -> m a
  addLocalRewrite r = liftThrough $ addLocalRewrite r

  default updateContext'
    :: (MonadAddContext n, MonadTransControl t, t n ~ m)
    => RefreshRews -> Substitution -> (Context -> Context) -> m a -> m a
  updateContext' r sub f = liftThrough $ updateContext' r sub f

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
