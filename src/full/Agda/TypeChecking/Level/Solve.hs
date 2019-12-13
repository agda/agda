{-# LANGUAGE ScopedTypeVariables #-}

module Agda.TypeChecking.Level.Solve where

import Control.Monad

import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import Data.Maybe

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.MetaVars

import Agda.TypeChecking.Level
import Agda.TypeChecking.MetaVars.Mention
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Except
import Agda.Utils.Monad

-- | Run the given action. At the end take all new metavariables of
--   type level for which the only constraints are upper bounds on the
--   level, and instantiate them to the lowest level.
defaultOpenLevelsToZero :: MonadMetaSolver m => m a -> m a
defaultOpenLevelsToZero f = ifNotM (optCumulativity <$> pragmaOptions) f $ do
  (result , newMetas) <- metasCreatedBy f
  defaultLevelsToZero newMetas
  return result

defaultLevelsToZero :: forall m. (MonadMetaSolver m) => IntSet -> m ()
defaultLevelsToZero xs = loop =<< openLevelMetas (map MetaId $ IntSet.elems xs)
  where
    loop :: [MetaId] -> m ()
    loop xs = do
      let isOpen x = isOpenMeta . mvInstantiation <$> lookupMeta x
      xs <- filterM isOpen xs
      allMetaTypes <- getOpenMetas >>= traverse metaType
      let notInTypeOfMeta x = not $ mentionsMeta x allMetaTypes
      progress <- forM xs $ \x -> do
        cs <- filter (mentionsMeta x) <$> getAllConstraints
        if | notInTypeOfMeta x , all (`isUpperBoundFor` x) cs -> do
               m <- lookupMeta x
               TelV tel t <- telView =<< metaType x
               addContext tel $ assignV DirEq x (teleArgs tel) (Level $ ClosedLevel 0) (AsTermsOf t)
               return True
             `catchError` \_ -> return False
           | otherwise -> return False

      if | or progress -> loop xs
         | otherwise   -> return ()

    openLevelMetas :: [MetaId] -> m [MetaId]
    openLevelMetas xs = return xs
      >>= filterM (\m -> isNothing <$> isInteractionMeta m)
      >>= filterM (\m -> (== NoGeneralize) <$> isGeneralizableMeta m)
      >>= filterM isLevelMeta

    isLevelMeta :: MetaId -> m Bool
    isLevelMeta x = do
      TelV tel t <- telView =<< metaType x
      addContext tel $ isLevelType t

    isUpperBoundFor :: ProblemConstraint -> MetaId -> Bool
    isUpperBoundFor c x = case clValue (theConstraint c) of
      LevelCmp CmpLeq l u -> not $ mentionsMeta x u
      _                   -> False
