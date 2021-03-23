
module Agda.TypeChecking.Monad.Open
        ( makeOpen
        , getOpen
        , tryGetOpen
        , isClosed
        ) where

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import Agda.Syntax.Internal
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad.Base

import {-# SOURCE #-} Agda.TypeChecking.Monad.Context

import Agda.Utils.Lens
import Agda.Utils.Maybe

-- | Create an open term in the current context.
makeOpen :: MonadTCEnv m => a -> m (Open a)
makeOpen x = do
    cp  <- viewTC eCurrentCheckpoint
    env <- viewTC eCheckpoints
    return $ OpenThing cp env x

-- | Extract the value from an open term. The checkpoint at which it was
--   created must be in scope.
getOpen :: (TermSubst a, MonadTCEnv m) => Open a -> m a
getOpen (OpenThing cp _ x) = do
  sub <- checkpointSubstitution cp
  return $ applySubst sub x

-- | Extract the value from an open term. If the checkpoint is no longer in scope use the provided
--   function to pull the object to the most recent common checkpoint. The function is given the
--   substitution from the common ancestor to the checkpoint of the thing.
tryGetOpen :: (TermSubst a, MonadTCEnv m) => (Substitution -> a -> Maybe a) -> Open a -> m (Maybe a)
tryGetOpen extract (OpenThing cp env x) = runMaybeT $ do
    (`applySubst` x) <$> (liftMaybe =<< viewTC (eCheckpoints . key cp))
  <|> do  -- Checkpoint no longer in scope
    curEnv <- lift $ viewTC eCheckpoints
    parent <- findParent env curEnv
    let Just subToOld = Map.lookup parent env
        Just subToCur = Map.lookup parent curEnv
    (applySubst subToCur) <$> liftMaybe (extract subToOld x)
  where
    findParent m1 m2
      | Set.null keys = empty
      | otherwise     = return $ Set.findMax keys
      where
        keys = Set.intersection (Map.keysSet m1) (Map.keysSet m2)

-- | An 'Open' is closed if it has checkpoint 0.
isClosed :: Open a -> Bool
isClosed (OpenThing cp _ _) = cp == 0
