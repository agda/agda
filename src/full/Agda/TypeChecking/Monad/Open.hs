
module Agda.TypeChecking.Monad.Open
        ( makeOpen
        , getOpen
        , tryGetOpen
        , isClosed
        ) where

import Agda.Syntax.Internal
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Base

import {-# SOURCE #-} Agda.TypeChecking.Monad.Context

import Agda.Utils.Lens

-- | Create an open term in the current context.
makeOpen :: MonadTCEnv m => a -> m (Open a)
makeOpen x = do
    cp <- viewTC eCurrentCheckpoint
    return $ OpenThing cp x

-- | Extract the value from an open term. The checkpoint at which it was
--   created must be in scope.
getOpen :: (Subst Term a, MonadTCEnv m) => Open a -> m a
getOpen (OpenThing cp x) = do
  sub <- checkpointSubstitution cp
  return $ applySubst sub x

-- | Extract the value from an open term. Returns `Nothing` if the checkpoint
--   at which it was created is not in scope.
tryGetOpen :: (Subst Term a, MonadTCEnv m) => Open a -> m (Maybe a)
tryGetOpen (OpenThing cp x) = fmap (`applySubst` x) <$> viewTC (eCheckpoints . key cp)

-- | An 'Open' is closed if it has checkpoint 0.
isClosed :: Open a -> Bool
isClosed (OpenThing cp _) = cp == 0
