{-# LANGUAGE ScopedTypeVariables #-}

module Agda.TypeChecking.Level.Solve where

import Control.Monad
import Control.Monad.Except

import qualified Data.Map.Strict as MapS
import Data.Maybe

import Agda.Interaction.Options

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.TypeChecking.Level
import Agda.TypeChecking.MetaVars.Mention
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Telescope

import Agda.Utils.Functor
import Agda.Utils.Monad

-- | Run the given action. At the end take all new metavariables of
--   type level for which the only constraints are upper bounds on the
--   level, and instantiate them to the lowest level.
defaultOpenLevelsToZero :: (PureTCM m, MonadMetaSolver m) => m a -> m a
defaultOpenLevelsToZero f = ifNotM (optCumulativity <$> pragmaOptions) f $ do
  (result, newMetas) <- metasCreatedBy f
  defaultLevelsToZero (openMetas newMetas)
  return result

defaultLevelsToZero ::
  forall m. (PureTCM m, MonadMetaSolver m) => LocalMetaStore -> m ()
defaultLevelsToZero xs = loop =<< openLevelMetas (MapS.keys xs)
  where
    loop :: [MetaId] -> m ()
    loop xs = do
      let isOpen x = isOpenMeta <$> lookupMetaInstantiation x
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

      when (or progress) $ (loop xs)

    openLevelMetas :: [MetaId] -> m [MetaId]
    openLevelMetas xs = filterM (isNothing <.> isInteractionMeta) xs
      >>= filterM (fmap (== NoGeneralize) . isGeneralizableMeta)
      >>= filterM isLevelMeta

    isLevelMeta :: MetaId -> m Bool
    isLevelMeta x = do
      TelV tel t <- telView =<< metaType x
      addContext tel $ isLevelType t

    isUpperBoundFor :: ProblemConstraint -> MetaId -> Bool
    isUpperBoundFor c x = case clValue (theConstraint c) of
      LevelCmp CmpLeq l u -> not $ mentionsMeta x u
      _                   -> False
