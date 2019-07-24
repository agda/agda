
module Agda.Syntax.Internal.MetaVars where

import Data.Monoid

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic

import Agda.Utils.Singleton

-- | Returns every meta-variable occurrence in the given type, except
-- for those in 'Sort's.
allMetas :: (TermLike a, Monoid m) => (MetaId -> m) -> a -> m
allMetas singl = foldTerm metas
  where
  metas (MetaV m _) = singl m
  metas (Level l)   = levelMetas l
  metas _           = mempty

  levelMetas (Max as) = foldMap plusLevelMetas as

  plusLevelMetas ClosedLevel{} = mempty
  plusLevelMetas (Plus _ l)    = levelAtomMetas l

  levelAtomMetas (MetaLevel m _) = singl m
  levelAtomMetas _               = mempty

-- | Returns 'allMetas' in a list.
--   @allMetasList = allMetas (:[])@.
--
--   Note: this resulting list is computed via difference lists.
--   Thus, use this function if you actually need the whole list of metas.
--   Otherwise, use 'allMetas' with a suitable monoid.
allMetasList :: TermLike a => a -> [MetaId]
allMetasList t = allMetas singleton t `appEndo` []

-- | 'True' if thing contains no metas.
--   @noMetas = null . allMetasList@.
noMetas :: TermLike a => a -> Bool
noMetas = getAll . allMetas (\ _m -> All False)

-- | Returns the first meta it find in the thing, if any.
--   @firstMeta == listToMaybe . allMetasList@.
firstMeta :: TermLike a => a -> Maybe MetaId
firstMeta = getFirst . allMetas (First . Just)
