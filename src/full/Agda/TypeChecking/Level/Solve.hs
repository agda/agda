{-# LANGUAGE ScopedTypeVariables #-}

module Agda.TypeChecking.Level.Solve where

import Control.Monad

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Level
import Agda.TypeChecking.MetaVars.Mention
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Except
import Agda.Utils.Monad

-- | Take all open metavariables of type level for which the only
--   constraints are upper bounds on the level, and instantiate them to
--   the lowest level.
defaultOpenLevelsToZero :: forall m. (MonadMetaSolver m) => m ()
defaultOpenLevelsToZero = do
  xs <- openLevelMetas
  progress <- forM xs $ \x -> do
    cs <- filter (mentionsMeta x) <$> getAllConstraints
    if | all (`isUpperBoundFor` x) cs -> do
           m <- lookupMeta x
           TelV tel t <- telView =<< metaType x
           addContext tel $ assignV DirEq x (teleArgs tel) $ Level (Max 0 [])
           return True
         `catchError` \_ -> return False
       | otherwise -> return False

  if | or progress -> defaultOpenLevelsToZero
     | otherwise   -> return ()

  where
    openLevelMetas :: m [MetaId]
    openLevelMetas = do
      ms <- getOpenMetas
      filterM isLevelMeta ms

    isLevelMeta :: MetaId -> m Bool
    isLevelMeta x = do
      TelV tel t <- telView =<< metaType x
      addContext tel $ isLevelType t

    isUpperBoundFor :: ProblemConstraint -> MetaId -> Bool
    isUpperBoundFor c x = case clValue (theConstraint c) of
      LevelCmp CmpLeq l u -> not $ mentionsMeta x u
      _                   -> False
