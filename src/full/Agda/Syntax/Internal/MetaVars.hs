{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Syntax.Internal.MetaVars where

import Data.Monoid
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Generic

import Agda.Utils.Singleton

-- | Returns every meta-variable occurrence in the given type, except
-- for those in sort annotations on types.
class AllMetas t where
  allMetas :: Monoid m => (MetaId -> m) -> t -> m

  default allMetas :: (TermLike t, Monoid m) => (MetaId -> m) -> t -> m
  allMetas = allMetas'

-- Default instances
instance AllMetas Term
instance AllMetas Type
instance TermLike a => AllMetas (Elim' a)
instance TermLike a => AllMetas (Tele a)

instance (AllMetas a, AllMetas b) => AllMetas (Dom' a b) where
  allMetas f (Dom _ _ _ t e) = allMetas f t <> allMetas f e

-- These types need to be packed up as a Term to get the metas.
instance AllMetas Sort      where allMetas f   = allMetas f . Sort
instance AllMetas Level     where allMetas f   = allMetas f . Level
instance AllMetas PlusLevel where allMetas f l = allMetas f (Max 0 [l])

instance {-# OVERLAPPING #-} AllMetas String where
  allMetas f _ = mempty

-- Generic instances
instance (AllMetas a, AllMetas b) => AllMetas (a, b) where
  allMetas f (x, y) = allMetas f x <> allMetas f y

instance (AllMetas a, AllMetas b, AllMetas c) => AllMetas (a, b, c) where
  allMetas f (x, y, z) = allMetas f (x, (y, z))

instance (AllMetas a, AllMetas b, AllMetas c, AllMetas d) => AllMetas (a, b, c, d) where
  allMetas f (x, y, z, w) = allMetas f (x, (y, (z, w)))

instance AllMetas a => AllMetas [a]       where allMetas f xs = foldMap (allMetas f) xs
instance AllMetas a => AllMetas (Maybe a) where allMetas f xs = foldMap (allMetas f) xs
instance AllMetas a => AllMetas (Arg a)   where allMetas f xs = foldMap (allMetas f) xs

allMetas' :: (TermLike a, Monoid m) => (MetaId -> m) -> a -> m
allMetas' singl = foldTerm metas
  where
  metas (MetaV m _) = singl m
  metas (Sort s)    = sortMetas s
  metas _           = mempty

  sortMetas Univ{}        = mempty
  sortMetas Inf{}         = mempty
  sortMetas SizeUniv{}    = mempty
  sortMetas LockUniv{}    = mempty
  sortMetas LevelUniv     = mempty
  sortMetas IntervalUniv{} = mempty
  sortMetas (PiSort _ s1 s2)  = sortMetas s1 <> sortMetas (unAbs s2)  -- the domain is a term so is covered by the fold
  sortMetas (FunSort a b) = sortMetas a <> sortMetas b
  sortMetas (UnivSort s)  = sortMetas s
  sortMetas (MetaS x _)   = singl x
  sortMetas DefS{}        = mempty
  sortMetas DummyS{}      = mempty

-- | Returns 'allMetas' in a list.
--   @allMetasList = allMetas (:[])@.
--
--   Note: this resulting list is computed via difference lists.
--   Thus, use this function if you actually need the whole list of metas.
--   Otherwise, use 'allMetas' with a suitable monoid.
allMetasList :: AllMetas a => a -> [MetaId]
allMetasList t = allMetas singleton t `appEndo` []

-- | 'True' if thing contains no metas.
--   @noMetas = null . allMetasList@.
noMetas :: AllMetas a => a -> Bool
noMetas = getAll . allMetas (\ _m -> All False)

-- | Returns the first meta it find in the thing, if any.
--   @firstMeta == listToMaybe . allMetasList@.
firstMeta :: AllMetas a => a -> Maybe MetaId
firstMeta = getFirst . allMetas (First . Just)

-- | A blocker that unblocks if any of the metas in a term are solved.
unblockOnAnyMetaIn :: AllMetas t => t -> Blocker
unblockOnAnyMetaIn t = unblockOnAnyMeta $ allMetas Set.singleton t

-- | A blocker that unblocks if any of the metas in a term are solved.
unblockOnAllMetasIn :: AllMetas t => t -> Blocker
unblockOnAllMetasIn t = unblockOnAllMetas $ allMetas Set.singleton t
