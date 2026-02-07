{-# OPTIONS_GHC -ddump-simpl -dsuppress-all -dno-suppress-type-signatures -ddump-to-file -dno-typeable-binds #-}
{-# OPTIONS_GHC -fworker-wrapper-cbv -ddump-stg-final #-}
{-# LANGUAGE UndecidableInstances #-} -- Due to underdetermined var in IsVarSet multi-param typeclass
{-# LANGUAGE MagicHash, UnboxedSums, UnboxedTuples #-}

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

module Agda.TypeChecking.FreeNew where
    -- ( VarCounts(..)
    -- , Free
    -- , IsVarSet(..)
    -- , SingleVar
    -- , pattern SingleVar
    -- , IgnoreSorts(..)
    -- , freeVars, freeVars', filterVarMap, filterVarMapToList
    -- , runFree, rigidVars, stronglyRigidVars, unguardedVars, allVars
    -- , flexibleVars
    -- , allFreeVars
    -- , allFreeVarsList
    -- , allRelevantVars, allRelevantVarsIgnoring
    -- , freeVarsIgnore
    -- , freeIn, freeInIgnoringSorts, isBinderUsed
    -- , relevantIn, relevantInIgnoringSortAnn
    -- , FlexRig'(..), FlexRig
    -- , LensFlexRig(..), isFlexible, isUnguarded, isStronglyRigid, isWeaklyRigid
    -- , VarOcc'(..), VarOcc
    -- , varOccurrenceIn
    -- , flexRigOccurrenceIn
    -- , closed
    -- , MetaSet
    -- , insertMetaSet, foldrMetaSet, metaSetToBlocker
    -- ) where

import Prelude hiding (null)

import Data.Semigroup ( Any(..), All(..) )
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap

import Agda.Benchmarking qualified as Bench

import Agda.Syntax.Common hiding (Arg, NamedArg)
import Agda.Syntax.Internal

import Agda.TypeChecking.Free.LazyNew
import Agda.Utils.VarSet (VarSet)
import Agda.Utils.VarSet qualified as VarSet
import Agda.Utils.Singleton
import Agda.Utils.StrictReader
import Agda.Utils.StrictEndo

-- ** Flex-rigid occurrence for a single variable
--------------------------------------------------------------------------------

data SingleFR = SingleFR !Int !FlexRig

instance LensFlexRig SingleFR MetaSet where
  lensFlexRig f (SingleFR x fr) = SingleFR x <$> f fr

data CollectSingleFR = CSFRNothing | CSFRJust !FlexRig

instance Semigroup CollectSingleFR where
  CSFRJust fr <> CSFRJust fr' = CSFRJust (addFlexRig fr fr')
  CSFRNothing <> s            = s
  s           <> CSFRNothing  = s

instance ComputeFree SingleFR where
  type FlexRigItem SingleFR = MetaSet
  type Collect SingleFR     = Endo CollectSingleFR
  underBinders' n (SingleFR x fr) = SingleFR (n + x) fr
  variable' x' (SingleFR x fr) = Endo \acc -> if x == x' then acc <> CSFRJust fr else acc
  ignoreSorts'      = IgnoreNot
  underConstructor' = defaultUnderConstructor
  underFlexRig'     = defaultUnderFlexRig
  underModality'  _ r = r
  underRelevance' _ r = r
  underQuantity'  _ r = r

{-# SPECIALIZE flexRigOccurrenceIn :: Nat -> Term -> Maybe FlexRig #-}
flexRigOccurrenceIn :: Free a => Nat -> a -> Maybe FlexRig
flexRigOccurrenceIn x a = case appEndo (runReader (freeVars a) (SingleFR x Unguarded)) CSFRNothing of
  CSFRNothing -> Nothing
  CSFRJust fr -> Just fr


-- -- ** Full occurence information for a single variable
-- --------------------------------------------------------------------------------

-- data SingleVar = SingleVar !Int !Int {-# UNPACK #-} !VarOcc
--   -- ^ Context size (level), variable we're interested in (level), FlexRig, Modality

-- instance LensModality SingleVar where
--   getModality (SingleVar _ _ occ)   = getModality occ
--   mapModality f (SingleVar l x occ) = SingleVar l x (mapModality f occ)

-- instance LensFlexRig SingleVar MetaSet where
--   lensFlexRig f (SingleVar l x occ) = SingleVar l x <$> lensFlexRig f occ

-- instance LensQuantity  SingleVar where
-- instance LensRelevance SingleVar where

-- data SingleVarOcc = SVONothing | SVOJust {-# UNPACK #-} !VarOcc

-- -- | Hereditary Semigroup instance.
-- --   (The default instance for 'Maybe' may not be the hereditary one.)
-- instance Semigroup SingleVarOcc where
--   SVOJust o  <> SVOJust o' = SVOJust (o <> o')
--   SVONothing <> s          = s
--   s          <> SVONothing = s

-- instance Monoid SingleVarOcc where
--   mempty = SVONothing

-- instance ComputeFree SingleVar where
--   type FlexRigItem SingleVar = MetaSet
--   type Collect SingleVar     = Endo SingleVarOcc
--   underBinders' n (SingleVar l x occ) = SingleVar (l + n) x occ
--   variable' x' (SingleVar l x occ) = Endo \acc ->
--     if l - x' - 1 == x then acc <> SVOJust occ
--                        else acc
--   ignoreSorts'      = IgnoreNot
--   underConstructor' = defaultUnderConstructor
--   underModality'    = defaultUnderModality
--   underRelevance'   = defaultUnderRelevance
--   underFlexRig'     = defaultUnderFlexRig
--   underQuantity'    = defaultUnderQuantity


-- -- | Get the full occurrence information of a free variable.
-- varOccurrenceIn :: forall a. Free a => Nat -> a -> Maybe VarOcc
-- varOccurrenceIn x a = case appEndo (runReader (freeVars a) (SingleVar _ _ _)) _ of
--   SVONothing  -> Nothing
--   SVOJust occ -> Just occ

-- ---------------------------------------------------------------------------
-- -- * Occurrence computation for a single variable.

-- -- ** Full free occurrence info for a single variable.

-- -- | Get the full occurrence information of a free variable.
-- varOccurrenceIn :: Free a => Nat -> a -> Maybe VarOcc
-- varOccurrenceIn = varOccurrenceIn' IgnoreNot

-- varOccurrenceIn' :: Free a => IgnoreSorts -> Nat -> a -> Maybe VarOcc
-- varOccurrenceIn' ig !x t = theSingleVarOcc $ runFree (SingleVar sg) ig t
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
--   withVarOcc o (SingleVarOcc x) = case x of
--     Nothing -> SingleVarOcc Nothing
--     Just x  -> SingleVarOcc (Just $! composeVarOcc o x)

-- -- ** Flexible /rigid occurrence info for a single variable.

-- -- | Get the full occurrence information of a free variable.
-- flexRigOccurrenceIn :: Free a => Nat -> a -> Maybe FlexRig
-- flexRigOccurrenceIn = flexRigOccurrenceIn' IgnoreNot

-- flexRigOccurrenceIn' :: Free a => IgnoreSorts -> Nat -> a -> Maybe FlexRig
-- flexRigOccurrenceIn' ig !x t = theSingleFlexRig $ runFree (SingleVar sg) ig t
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
--   SingleFlexRig (Just o) <> SingleFlexRig (Just o') = SingleFlexRig $! Just $! addFlexRig o o'

-- instance Monoid SingleFlexRig where
--   mempty = SingleFlexRig Nothing
--   mappend = (<>)

-- instance IsVarSet MetaSet SingleFlexRig where
--   withVarOcc o (SingleFlexRig x) = case x of
--     Nothing -> SingleFlexRig Nothing
--     Just x  -> SingleFlexRig (Just $! composeFlexRig (varFlexRig o) x)

-- -- ** Plain free occurrence.
-- -- | Check if a variable is free, possibly ignoring sorts
-- freeIn' :: Free a => IgnoreSorts -> Nat -> a -> Bool
-- freeIn' ig !x t = getAny $ runFree (SingleVar (Any . (x ==))) ig t

-- freeIn :: Free a => Nat -> a -> Bool
-- freeIn = freeIn' IgnoreNot

-- freeInIgnoringSorts :: Free a => Nat -> a -> Bool
-- freeInIgnoringSorts = freeIn' IgnoreAll

-- -- UNUSED Liang-Ting Chen 2019-07-16
-- --freeInIgnoringSortAnn :: Free a => Nat -> a -> Bool
-- --freeInIgnoringSortAnn = freeIn' IgnoreInAnnotations

-- -- | Is the variable bound by the abstraction actually used?
-- isBinderUsed :: Free a => Abs a -> Bool
-- isBinderUsed NoAbs{}   = False
-- isBinderUsed (Abs _ x) = 0 `freeIn` x

-- -- ** Relevant free occurrence.

-- newtype RelevantIn c = RelevantIn {getRelevantIn :: c}
--   deriving (Semigroup, Monoid)

-- instance IsVarSet a c => IsVarSet a (RelevantIn c) where  -- UndecidableInstances
--   withVarOcc o x
--     | isIrrelevant o = mempty
--     | otherwise = RelevantIn $! withVarOcc o $! getRelevantIn x

-- relevantIn' :: Free t => IgnoreSorts -> Nat -> t -> Bool
-- relevantIn' ig !x t =
--   getAny . getRelevantIn $ runFree (SingleVar (RelevantIn . Any . (x ==))) ig t

-- relevantInIgnoringSortAnn :: Free t => Nat -> t -> Bool
-- relevantInIgnoringSortAnn = relevantIn' IgnoreInAnnotations

-- relevantIn :: Free t => Nat -> t -> Bool
-- relevantIn = relevantIn' IgnoreAll

-- ---------------------------------------------------------------------------
-- -- * Occurrences of all free variables.

-- -- | Is the term entirely closed (no free variables)?
-- closed :: Free t => t -> Bool
-- closed t = getAll $ runFree (SingleVar (const $ All False)) IgnoreNot t

-- -- | Collect all free variables.
-- allFreeVars :: Free t => t -> VarSet
-- allFreeVars = runFree (SingleVar singleton) IgnoreNot

-- -- | Collect all free variables in order in a list.
-- allFreeVarsList :: Free t => t -> [Int]
-- allFreeVarsList t = runFree (SingleVar \x -> Endo (x:)) IgnoreNot t `appEndo` []

-- -- | Collect all relevant free variables, possibly ignoring sorts.
-- allRelevantVarsIgnoring :: Free t => IgnoreSorts -> t -> VarSet
-- allRelevantVarsIgnoring ig =
--   getRelevantIn . runFree (SingleVar (RelevantIn . singleton)) ig

-- -- | Collect all relevant free variables, excluding the "unused" ones.
-- allRelevantVars :: Free t => t -> VarSet
-- allRelevantVars = allRelevantVarsIgnoring IgnoreNot

-- ---------------------------------------------------------------------------
-- -- * Backwards-compatible interface to 'freeVars'.

-- filterVarMap :: (VarOcc -> Bool) -> VarMap -> VarSet
-- filterVarMap f = VarSet.fromList . IntMap.keys . IntMap.filter f . theVarMap

-- filterVarMapToList :: (VarOcc -> Bool) -> VarMap -> [Variable]
-- filterVarMapToList f = map fst . filter (f . snd) . IntMap.toList . theVarMap

-- -- | Variables under only and at least one inductive constructor(s).
-- stronglyRigidVars :: VarMap -> VarSet
-- stronglyRigidVars = filterVarMap $ \case
--   VarOcc StronglyRigid _ -> True
--   _ -> False

-- -- | Variables at top or only under inductive record constructors
-- --   λs and Πs.
-- --   The purpose of recording these separately is that they
-- --   can still become strongly rigid if put under a constructor
-- --   whereas weakly rigid ones stay weakly rigid.
-- unguardedVars :: VarMap -> VarSet
-- unguardedVars = filterVarMap $ \case
--   VarOcc Unguarded _ -> True
--   _ -> False

-- -- UNUSED Liang-Ting Chen 2019-07-16
-- ---- | Ordinary rigid variables, e.g., in arguments of variables or functions.
-- --weaklyRigidVars :: VarMap -> VarSet
-- --weaklyRigidVars = filterVarMap $ \case
-- --  VarOcc WeaklyRigid _ -> True
-- --  _ -> False

-- -- | Rigid variables: either strongly rigid, unguarded, or weakly rigid.
-- rigidVars :: VarMap -> VarSet
-- rigidVars = filterVarMap $ \case
--   VarOcc o _ -> o `elem` [ WeaklyRigid, Unguarded, StronglyRigid ]

-- -- | Variables occuring in arguments of metas.
-- --  These are only potentially free, depending how the meta variable is instantiated.
-- --  The set contains the id's of the meta variables that this variable is an argument to.
-- flexibleVars :: VarMap -> IntMap MetaSet
-- flexibleVars (VarMap m) = (`IntMap.mapMaybe` m) $ \case
--  VarOcc (Flexible ms) _ -> Just ms
--  _ -> Nothing

-- ---- | Variables in irrelevant arguments and under a @DontCare@, i.e.,
-- ----   in irrelevant positions.
-- --irrelevantVars :: VarMap -> VarSet
-- --irrelevantVars = filterVarMap isIrrelevant

-- allVars :: VarMap -> VarSet
-- allVars = VarSet.fromList . IntMap.keys . theVarMap
