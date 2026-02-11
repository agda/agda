{-# LANGUAGE UndecidableInstances       #-} -- Due to underdetermined var in IsVarSet multi-param typeclass

-- | Computing the free variables of a term.
--
-- The distinction between rigid and strongly rigid occurrences comes from:
--   Jason C. Reed, PhD thesis, 2009, page 96 (see also his LFMTP 2009 paper)
--
-- The main idea is that x = t(x) is unsolvable if x occurs strongly rigidly
-- in t.  It might have a solution if the occurrence is not strongly rigid, e.g.
--
--   x = \f -> suc (f (x (\ y -> k)))  has  x = \f -> suc (f (suc k))
--
-- [Jason C. Reed, PhD thesis, page 106]
--
-- Under coinductive constructors, occurrences are never strongly rigid.
-- Also, function types and lambdas do not establish strong rigidity.
-- Only inductive constructors do so.
-- (See issue 1271).
--
-- If you need the occurrence information for all free variables, you can use
-- @freeVars@ which has amoungst others this instance
-- @
--    freeVars :: Term -> VarMap
-- @
-- From @VarMap@, specific information can be extracted, e.g.,
-- @
--    relevantVars :: VarMap -> VarSet
--    relevantVars = filterVarMap isRelevant
-- @
--
-- To just check the status of a single free variable, there are more
-- efficient methods, e.g.,
-- @
--    freeIn :: Nat -> Term -> Bool
-- @
--
-- Tailored optimized variable checks can be implemented as semimodules to 'VarOcc',
-- see, for example, 'VarCounts' or 'SingleFlexRig'.

module Agda.TypeChecking.Free
    (
      FlexRig
    , FlexRig'(..)
    , Free
    , IgnoreSorts(..)
    , IsVarSet(..)
    , LensFlexRig(..)
    , VarCounts(..)

    , allVars
    , filterVarMap
    , filterVarMapToList
    , flexibleVars
    , isFlexible
    , isStronglyRigid
    , isUnguarded
    , isWeaklyRigid
    , rigidVars
    , stronglyRigidVars
    , unguardedVars

    , MetaSet
    , foldrMetaSet
    , insertMetaSet
    , metaSetToBlocker

    , allFreeVar
    , allFreeVarIgnoreAll
    , anyFreeVar
    , anyFreeVarIgnoreAll
    , closed
    , flexRigOccurrenceIn
    , freeIn
    , freeInIgnoringSorts
    , freeVarCounts
    , freeVarList
    , freeVarMap
    , freeVarMapIgnoreAnn
    , freeVarSet
    , isBinderUsed
    , relevantInIgnoringSortAnn
    ) where

import Prelude hiding (null)

import Data.Semigroup ( Any(..), All(..) )
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import qualified Agda.Benchmarking as Bench

import Agda.Syntax.Common hiding (Arg, NamedArg)
import Agda.Syntax.Internal

import Agda.TypeChecking.Free.Lazy hiding (Free)
import Agda.TypeChecking.Free.Lazy qualified as FreeOld
import Agda.TypeChecking.Free.LazyNew qualified as FreeNew
import Agda.TypeChecking.FreeNew qualified as FreeNew

import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as VarSet
import Agda.Utils.Singleton
import Agda.Utils.Impossible

import Debug.Trace
import Agda.Syntax.Position

-- New API
--------------------------------------------------------------------------------

-- type Free a = (FreeOld.Free a, FreeNew.Free a)
type Free a = (FreeNew.Free a)

freeIn :: Free t => Int -> t -> Bool
freeIn x t =
  let
    -- r = oldFreeIn x t
    r' = FreeNew.freeIn x t
  in
    -- if r == r' then
      r'
    -- else
    --   __IMPOSSIBLE__

flexRigOccurrenceIn :: Free t => Int -> t -> Maybe FlexRig
flexRigOccurrenceIn x t =
  let
    -- r = oldFlexRigOccurrenceIn x t
    r' = FreeNew.flexRigOccurrenceIn x t
  in
    -- if r == r' then
      r'
    -- else
    --   __IMPOSSIBLE__

relevantInIgnoringSortAnn :: Free t => Nat -> t -> Bool
relevantInIgnoringSortAnn x t =
  let
    -- r = oldRelevantInIgnoringSortAnn x t
    r' = FreeNew.relevantInIgnoringSortAnn x t
  in
    -- if r == r' then
      r'
    -- else
    --   __IMPOSSIBLE__

freeInIgnoringSorts :: Free a => Nat -> a -> Bool
freeInIgnoringSorts x t =
  let
    -- r = oldFreeInIgnoringSorts x t
    r' = FreeNew.freeInIgnoringSorts x t
  in
    -- if r == r' then
      r'
    -- else
    --   __IMPOSSIBLE__

isBinderUsed :: Free a => Abs a -> Bool
isBinderUsed NoAbs{}   = False
isBinderUsed (Abs _ x) = 0 `freeIn` x

closed :: Free t => t -> Bool
closed t =
  let
    -- r  = oldClosed t
    r' = FreeNew.closed t
  in
    -- if r == r' then
      r'
    -- else
    --   __IMPOSSIBLE__

anyFreeVar :: Free t => (Int -> Bool) -> t -> Bool
anyFreeVar f t =
  let
      -- r  = getAny $ runFree (Any . f) IgnoreNot t
      r' = FreeNew.anyFreeVar f t
  in
    -- if r == r' then
      r'
    -- else
    --   __IMPOSSIBLE__

allFreeVar :: Free t => (Int -> Bool) -> t -> Bool
allFreeVar f t =
  let
      -- r  = getAll $ runFree (All . f) IgnoreNot t
      r' = FreeNew.allFreeVar f t
  in
    -- if r == r' then
      r'
    -- else
    --   __IMPOSSIBLE__

anyFreeVarIgnoreAll :: Free t => (Int -> Bool) -> t -> Bool
anyFreeVarIgnoreAll f t =
  let
      -- r = getAny $ runFree (Any . f) IgnoreAll t
      r' = FreeNew.anyFreeVarIgnoreAll f t
  in
    -- if r == r' then
      r'
    -- else
    --   __IMPOSSIBLE__

allFreeVarIgnoreAll :: Free t => (Int -> Bool) -> t -> Bool
allFreeVarIgnoreAll f t =
  let
      -- r  = getAll $ runFree (All . f) IgnoreAll t
      r' = FreeNew.allFreeVarIgnoreAll f t
  in
    -- if r == r' then
      r'
    -- else
    --   __IMPOSSIBLE__

freeVarMap :: Free t => t -> VarMap
freeVarMap t =
  let
      -- r :: VarMap
      -- r  = freeVars t
      r' :: VarMap
      r' = FreeNew.freeVarMap t
  in
    -- if r == r' then
      r'
    -- else
    --   trace ("FREEVARMAP\n" ++ show (killRange t) ++ "\n\n" ++ show r ++ "\n\n" ++ show r') __IMPOSSIBLE__

freeVarMapIgnoreAnn :: Free t => t -> VarMap
freeVarMapIgnoreAnn t =
  let
      -- r :: VarMap
      -- r = freeVarsIgnore IgnoreInAnnotations t
      r' :: VarMap
      r' = FreeNew.freeVarMapIgnoreAnn t
  in
    -- if r == r' then
      r'
    -- else
    --   trace ("FREEVARMAPIGANN\n" ++ show (killRange t) ++ "\n\n" ++ show r ++ "\n\n" ++ show r') __IMPOSSIBLE__

freeVarCounts :: Free t => t -> VarCounts
freeVarCounts t =
  let
      -- r :: VarCounts
      -- r  = freeVars t
      r' :: VarCounts
      r' = FreeNew.freeVarCounts t
  in
    -- if r == r' then
      r'
    -- else
    --   trace ("FREEVARCOUNTS\n" ++ show r ++ "\n\n" ++ show r') __IMPOSSIBLE__

freeVarSet :: Free t => t -> VarSet
freeVarSet t =
  let
      -- r  = freeVars t
      r' = FreeNew.freeVarSet t
  in
    -- if r == r' then
      r'
    -- else
    --   __IMPOSSIBLE__

freeVarList :: Free t => t -> [Int]
freeVarList t =
  let
      -- r  = freeVars t
      r' = FreeNew.freeVarList t
  in
    -- if r == r' then
      r'
    -- else
    --   __IMPOSSIBLE__

-- ---------------------------------------------------------------------------
-- -- * Simple variable set implementations.


-- -- In most cases we don't care about the VarOcc.

-- instance IsVarSet () VarSet where withVarOcc _ = id
-- instance IsVarSet () [Int]  where withVarOcc _ = id
-- instance IsVarSet () Any    where withVarOcc _ = id
-- instance IsVarSet () All    where withVarOcc _ = id

-- ---------------------------------------------------------------------------
-- -- * Collecting free variables (generic).

-- -- | Collect all free variables together with information about their occurrence.
-- --
-- -- Doesn't go inside solved metas, but collects the variables from a
-- -- metavariable application @X ts@ as @flexibleVars@.
-- {-# SPECIALIZE freeVars :: FreeOld.Free a => a -> VarMap #-}
-- freeVars :: (IsVarSet a c, Singleton Variable c, FreeOld.Free t) => t -> c
-- freeVars = freeVarsIgnore IgnoreNot

-- freeVarsIgnore :: (IsVarSet a c, Singleton Variable c, FreeOld.Free t) =>
--                   IgnoreSorts -> t -> c
-- freeVarsIgnore = runFree singleton

-- -- Specialization to typical monoids
-- {-# SPECIALIZE runFree :: FreeOld.Free a => SingleVar Any -> IgnoreSorts -> a -> Any #-}
-- -- Specialization to Term
-- {-# SPECIALIZE runFree :: SingleVar Any -> IgnoreSorts -> Term -> Any #-}

-- -- | Compute free variables.
-- runFree :: (IsVarSet a c, FreeOld.Free t) => SingleVar c -> IgnoreSorts -> t -> c
-- runFree single i t = -- bench $  -- Benchmarking is expensive (4% on std-lib)
--   runFreeM single i (freeVars' t)
--   where
--   bench = Bench.billToPure [ Bench.Typing , Bench.Free ]

-- ---------------------------------------------------------------------------
-- -- * Occurrence computation for a single variable.

-- -- ** Full free occurrence info for a single variable.

-- -- | Get the full occurrence information of a free variable.
-- varOccurrenceIn :: FreeOld.Free a => Nat -> a -> Maybe VarOcc
-- varOccurrenceIn = varOccurrenceIn' IgnoreNot

-- varOccurrenceIn' :: FreeOld.Free a => IgnoreSorts -> Nat -> a -> Maybe VarOcc
-- varOccurrenceIn' ig x t = theSingleVarOcc $ runFree sg ig t
--   where
--   sg y = if x == y then oneSingleVarOcc else mempty

-- -- | "Collection" just keeping track of the occurrence of a single variable.
-- --   'Nothing' means variable does not occur freely.
-- newtype SingleVarOcc = SingleVarOcc { theSingleVarOcc :: Maybe VarOcc }

-- oneSingleVarOcc :: SingleVarOcc
-- oneSingleVarOcc = SingleVarOcc $ Just $ oneVarOcc

-- -- | Hereditary Semigroup instance for 'Maybe'.
-- --   (The default instance for 'Maybe' may not be the hereditary one.)
-- instance Semigroup SingleVarOcc where
--   SingleVarOcc Nothing <> s = s
--   s <> SingleVarOcc Nothing = s
--   SingleVarOcc (Just o) <> SingleVarOcc (Just o') = SingleVarOcc $ Just $ o <> o'

-- instance Monoid SingleVarOcc where
--   mempty = SingleVarOcc Nothing
--   mappend = (<>)

-- instance IsVarSet MetaSet SingleVarOcc where
--   withVarOcc o = SingleVarOcc . fmap (composeVarOcc o) . theSingleVarOcc

-- -- ** Flexible /rigid occurrence info for a single variable.

-- -- | Get the full occurrence information of a free variable.
-- oldFlexRigOccurrenceIn :: FreeOld.Free a => Nat -> a -> Maybe FlexRig
-- oldFlexRigOccurrenceIn = flexRigOccurrenceIn' IgnoreNot

-- flexRigOccurrenceIn' :: FreeOld.Free a => IgnoreSorts -> Nat -> a -> Maybe FlexRig
-- flexRigOccurrenceIn' ig x t = theSingleFlexRig $ runFree sg ig t
--   where
--   sg y = if x == y then oneSingleFlexRig else mempty

-- -- | "Collection" just keeping track of the occurrence of a single variable.
-- --   'Nothing' means variable does not occur freely.
-- newtype SingleFlexRig = SingleFlexRig { theSingleFlexRig :: Maybe FlexRig }

-- oneSingleFlexRig :: SingleFlexRig
-- oneSingleFlexRig = SingleFlexRig $ Just $ oneFlexRig

-- -- | Hereditary Semigroup instance for 'Maybe'.
-- --   (The default instance for 'Maybe' may not be the hereditary one.)
-- instance Semigroup SingleFlexRig where
--   SingleFlexRig Nothing <> s = s
--   s <> SingleFlexRig Nothing = s
--   SingleFlexRig (Just o) <> SingleFlexRig (Just o') = SingleFlexRig $ Just $ addFlexRig o o'

-- instance Monoid SingleFlexRig where
--   mempty = SingleFlexRig Nothing
--   mappend = (<>)

-- instance IsVarSet MetaSet SingleFlexRig where
--   withVarOcc o = SingleFlexRig . fmap (composeFlexRig $ varFlexRig o) . theSingleFlexRig

-- -- ** Plain free occurrence.

-- -- | Check if a variable is free, possibly ignoring sorts.
-- freeIn' :: FreeOld.Free a => IgnoreSorts -> Nat -> a -> Bool
-- freeIn' ig x t = getAny $ runFree (Any . (x ==)) ig t

-- {-# SPECIALIZE oldFreeIn :: Nat -> Term -> Bool #-}
-- oldFreeIn :: FreeOld.Free a => Nat -> a -> Bool
-- oldFreeIn = freeIn' IgnoreNot

-- oldFreeInIgnoringSorts :: FreeOld.Free a => Nat -> a -> Bool
-- oldFreeInIgnoringSorts = freeIn' IgnoreAll

-- -- UNUSED Liang-Ting Chen 2019-07-16
-- --freeInIgnoringSortAnn :: FreeOld.Free a => Nat -> a -> Bool
-- --freeInIgnoringSortAnn = freeIn' IgnoreInAnnotations

-- -- | Is the variable bound by the abstraction actually used?
-- oldIsBinderUsed :: FreeOld.Free a => Abs a -> Bool
-- oldIsBinderUsed NoAbs{}   = False
-- oldIsBinderUsed (Abs _ x) = 0 `oldFreeIn` x

-- -- ** Relevant free occurrence.

-- newtype RelevantIn c = RelevantIn {getRelevantIn :: c}
--   deriving (Semigroup, Monoid)

-- instance IsVarSet a c => IsVarSet a (RelevantIn c) where  -- UndecidableInstances
--   withVarOcc o x
--     | isIrrelevant o = mempty
--     | otherwise = RelevantIn $ withVarOcc o $ getRelevantIn x

-- relevantIn' :: FreeOld.Free t => IgnoreSorts -> Nat -> t -> Bool
-- relevantIn' ig x t = getAny . getRelevantIn $ runFree (RelevantIn . Any . (x ==)) ig t

-- oldRelevantInIgnoringSortAnn :: FreeOld.Free t => Nat -> t -> Bool
-- oldRelevantInIgnoringSortAnn = relevantIn' IgnoreInAnnotations

-- relevantIn :: FreeOld.Free t => Nat -> t -> Bool
-- relevantIn = relevantIn' IgnoreAll

-- ---------------------------------------------------------------------------
-- -- * Occurrences of all free variables.

-- -- | Is the term entirely closed (no free variables)?
-- oldClosed :: FreeOld.Free t => t -> Bool
-- oldClosed t = getAll $ runFree (const $ All False) IgnoreNot t

-- -- | Collect all free variables.
-- allFreeVars :: FreeOld.Free t => t -> VarSet
-- allFreeVars = runFree singleton IgnoreNot

-- -- | Collect all relevant free variables, possibly ignoring sorts.
-- allRelevantVarsIgnoring :: FreeOld.Free t => IgnoreSorts -> t -> VarSet
-- allRelevantVarsIgnoring ig = getRelevantIn . runFree (RelevantIn . singleton) ig

-- -- | Collect all relevant free variables, excluding the "unused" ones.
-- allRelevantVars :: FreeOld.Free t => t -> VarSet
-- allRelevantVars = allRelevantVarsIgnoring IgnoreNot


---------------------------------------------------------------------------
-- * Backwards-compatible interface to 'freeVars'.

{-# INLINE filterVarMap #-}
filterVarMap :: (VarOcc -> Bool) -> VarMap -> VarSet
filterVarMap f = \(VarMap m) ->
  IntMap.foldlWithKey'
  (\acc k v -> if f v then VarSet.insert k acc else acc)
  mempty m

{-# INLINE filterVarMapToList #-}
filterVarMapToList :: (VarOcc -> Bool) -> VarMap -> [Int]
filterVarMapToList f = \(VarMap m) ->
  IntMap.foldrWithKey'
  (\k v acc -> if f v then k:acc else acc)
  [] m

-- | Variables under only and at least one inductive constructor(s).
stronglyRigidVars :: VarMap -> VarSet
stronglyRigidVars = filterVarMap $ \case
  VarOcc StronglyRigid _ -> True
  _                      -> False

-- | Variables at top or only under inductive record constructors
--   λs and Πs.
--   The purpose of recording these separately is that they
--   can still become strongly rigid if put under a constructor
--   whereas weakly rigid ones stay weakly rigid.
unguardedVars :: VarMap -> VarSet
unguardedVars = filterVarMap $ \case
  VarOcc Unguarded _ -> True
  _                  -> False

-- | Rigid variables: either strongly rigid, unguarded, or weakly rigid.
rigidVars :: VarMap -> VarSet
rigidVars = filterVarMap $ \case
  VarOcc o _ -> case o of
    WeaklyRigid   -> True
    Unguarded     -> True
    StronglyRigid -> True
    _             -> False

-- | Variables occuring in arguments of metas.
--  These are only potentially free, depending how the meta variable is instantiated.
--  The set contains the id's of the meta variables that this variable is an argument to.
flexibleVars :: VarMap -> IntMap MetaSet
flexibleVars (VarMap m) = flip IntMap.mapMaybe m $ \case
 VarOcc (Flexible ms) _ -> Just ms
 _                      -> Nothing

allVars :: VarMap -> VarSet
allVars = filterVarMap (\_ -> True)
