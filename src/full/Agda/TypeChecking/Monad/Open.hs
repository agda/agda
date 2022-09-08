
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
import Agda.TypeChecking.Monad.State (currentModuleNameHash)

import {-# SOURCE #-} Agda.TypeChecking.Monad.Context

import Agda.Utils.Lens
import Agda.Utils.Maybe

-- | Create an open term in the current context.
makeOpen :: (ReadTCState m, MonadTCEnv m) => a -> m (Open a)
makeOpen x = do
    cp  <- viewTC eCurrentCheckpoint
    env <- viewTC eCheckpoints
    m   <- currentModuleNameHash
    return $ OpenThing cp env m x

-- | Extract the value from an open term. The checkpoint at which it was
--   created must be in scope.
getOpen :: (TermSubst a, MonadTCEnv m) => Open a -> m a
getOpen (OpenThing cp _ _ x) = do
  sub <- checkpointSubstitution cp
  return $ applySubst sub x

-- | Extract the value from an open term. If the checkpoint is no longer in scope use the provided
--   function to pull the object to the most recent common checkpoint. The function is given the
--   substitution from the common ancestor to the checkpoint of the thing.
tryGetOpen :: (TermSubst a, ReadTCState m, MonadTCEnv m) => (Substitution -> a -> Maybe a) -> Open a -> m (Maybe a)
tryGetOpen extract open = do
  OpenThing cp env _ x <- restrict open -- Strip the env if from another module
  runMaybeT $ do
      (`applySubst` x) <$> (liftMaybe =<< viewTC (eCheckpoints . key cp))
    <|> do  -- Checkpoint no longer in scope
      curEnv <- lift $ viewTC eCheckpoints
      parent <- findParent env curEnv
      let Just subToOld = Map.lookup parent env
          Just subToCur = Map.lookup parent curEnv
      (applySubst subToCur) <$> liftMaybe (extract subToOld x)
  where
    -- If this comes from a different file, the checkpoints refer to checkpoints in that file and
    -- not in the current file. To avoid confusing them we set the checkpoint to -1 and only keep
    -- checkpoint 0 (which is shared between files) in the environment.
    restrict o@(OpenThing cp env m x) = do
      cur <- currentModuleNameHash
      if m == cur then return o
                  else return $ OpenThing (-1) (Map.filterWithKey (\ k _ -> k == 0) env) m x

    findParent m1 m2 = case Map.lookupMax (Map.intersection m1 m2) of
      Nothing       -> empty
      Just (max, _) -> return max

-- | An 'Open' is closed if it has checkpoint 0.
isClosed :: Open a -> Bool
isClosed (OpenThing cp _ _ _) = cp == 0
