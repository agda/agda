{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances       #-}

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
    ( VarCounts(..)
    , Free
    , IsVarSet(..)
    , IgnoreSorts(..)
    , freeVars, freeVars', filterVarMap, filterVarMapToList
    , runFree, rigidVars, stronglyRigidVars, unguardedVars, allVars
    , allFreeVars
    , allRelevantVars, allRelevantVarsIgnoring
    , freeIn, freeInIgnoringSorts, isBinderUsed
    , relevantIn, relevantInIgnoringSortAnn
    , FlexRig'(..), FlexRig
    , LensFlexRig(..), isFlexible, isUnguarded, isStronglyRigid, isWeaklyRigid
    , VarOcc'(..), VarOcc
    , varOccurrenceIn
    , flexRigOccurrenceIn
    , closed
    , MetaSet
    , insertMetaSet, foldrMetaSet
    ) where

import Prelude hiding (null)




import Data.Monoid ( Monoid, mempty, mappend)
import Data.Semigroup ( Semigroup, (<>), Any(..), All(..) )
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap



import qualified Agda.Benchmarking as Bench

import Agda.Syntax.Common hiding (Arg, NamedArg)
import Agda.Syntax.Internal

import Agda.TypeChecking.Free.Lazy
  -- ( Free(..) , FreeEnv(..), initFreeEnv
  -- , FlexRig, FlexRig'(..)
  -- , VarOcc(..), topVarOcc, TheVarMap, theVarMap, IgnoreSorts(..), Variable, SingleVar
  -- , MetaSet, insertMetaSet, foldrMetaSet
  -- , IsVarSet(..), runFreeM
  -- )

import Agda.Utils.Singleton

---------------------------------------------------------------------------
-- * Simple variable set implementations.

type VarSet = IntSet

-- In most cases we don't care about the VarOcc.

instance IsVarSet () VarSet where withVarOcc _ = id
instance IsVarSet () [Int]  where withVarOcc _ = id
instance IsVarSet () Any    where withVarOcc _ = id
instance IsVarSet () All    where withVarOcc _ = id

---------------------------------------------------------------------------
-- * Plain variable occurrence counting.

newtype VarCounts = VarCounts { varCounts :: IntMap Int }

instance Semigroup VarCounts where
  VarCounts fv1 <> VarCounts fv2 = VarCounts (IntMap.unionWith (+) fv1 fv2)

instance Monoid VarCounts where
  mempty = VarCounts IntMap.empty
  mappend = (<>)

instance IsVarSet () VarCounts where
  withVarOcc _ = id

instance Singleton Variable VarCounts where
  singleton i = VarCounts $ IntMap.singleton i 1

---------------------------------------------------------------------------
-- * Collecting free variables (generic).

-- | Collect all free variables together with information about their occurrence.
--
-- Doesn't go inside solved metas, but collects the variables from a
-- metavariable application @X ts@ as @flexibleVars@.
{-# SPECIALIZE freeVars :: Free a => a -> VarMap #-}
freeVars :: (IsVarSet a c, Singleton Variable c, Free t) => t -> c
freeVars = freeVarsIgnore IgnoreNot

freeVarsIgnore :: (IsVarSet a c, Singleton Variable c, Free t) =>
                  IgnoreSorts -> t -> c
freeVarsIgnore = runFree singleton

-- Specialization to typical monoids
{-# SPECIALIZE runFree :: Free a => SingleVar Any      -> IgnoreSorts -> a -> Any #-}
-- Specialization to Term
{-# SPECIALIZE runFree :: SingleVar Any      -> IgnoreSorts -> Term -> Any #-}

-- | Compute free variables.
runFree :: (IsVarSet a c, Free t) => SingleVar c -> IgnoreSorts -> t -> c
runFree single i t = -- bench $  -- Benchmarking is expensive (4% on std-lib)
  runFreeM single i (freeVars' t)
  where
  bench = Bench.billToPure [ Bench.Typing , Bench.Free ]

---------------------------------------------------------------------------
-- * Occurrence computation for a single variable.

-- ** Full free occurrence info for a single variable.

-- | Get the full occurrence information of a free variable.
varOccurrenceIn :: Free a => Nat -> a -> Maybe VarOcc
varOccurrenceIn = varOccurrenceIn' IgnoreNot

varOccurrenceIn' :: Free a => IgnoreSorts -> Nat -> a -> Maybe VarOcc
varOccurrenceIn' ig x t = theSingleVarOcc $ runFree sg ig t
  where
  sg y = if x == y then oneSingleVarOcc else mempty

-- | "Collection" just keeping track of the occurrence of a single variable.
--   'Nothing' means variable does not occur freely.
newtype SingleVarOcc = SingleVarOcc { theSingleVarOcc :: Maybe VarOcc }

oneSingleVarOcc :: SingleVarOcc
oneSingleVarOcc = SingleVarOcc $ Just $ oneVarOcc

-- | Hereditary Semigroup instance for 'Maybe'.
--   (The default instance for 'Maybe' may not be the hereditary one.)
instance Semigroup SingleVarOcc where
  SingleVarOcc Nothing <> s = s
  s <> SingleVarOcc Nothing = s
  SingleVarOcc (Just o) <> SingleVarOcc (Just o') = SingleVarOcc $ Just $ o <> o'

instance Monoid SingleVarOcc where
  mempty = SingleVarOcc Nothing
  mappend = (<>)

instance IsVarSet MetaSet SingleVarOcc where
  withVarOcc o = SingleVarOcc . fmap (composeVarOcc o) . theSingleVarOcc

-- ** Flexible /rigid occurrence info for a single variable.

-- | Get the full occurrence information of a free variable.
flexRigOccurrenceIn :: Free a => Nat -> a -> Maybe (FlexRig' ())
flexRigOccurrenceIn = flexRigOccurrenceIn' IgnoreNot

flexRigOccurrenceIn' :: Free a => IgnoreSorts -> Nat -> a -> Maybe (FlexRig' ())
flexRigOccurrenceIn' ig x t = theSingleFlexRig $ runFree sg ig t
  where
  sg y = if x == y then oneSingleFlexRig else mempty

-- | "Collection" just keeping track of the occurrence of a single variable.
--   'Nothing' means variable does not occur freely.
newtype SingleFlexRig = SingleFlexRig { theSingleFlexRig :: Maybe (FlexRig' ()) }

oneSingleFlexRig :: SingleFlexRig
oneSingleFlexRig = SingleFlexRig $ Just $ oneFlexRig

-- | Hereditary Semigroup instance for 'Maybe'.
--   (The default instance for 'Maybe' may not be the hereditary one.)
instance Semigroup SingleFlexRig where
  SingleFlexRig Nothing <> s = s
  s <> SingleFlexRig Nothing = s
  SingleFlexRig (Just o) <> SingleFlexRig (Just o') = SingleFlexRig $ Just $ addFlexRig o o'

instance Monoid SingleFlexRig where
  mempty = SingleFlexRig Nothing
  mappend = (<>)

instance IsVarSet () SingleFlexRig where
  withVarOcc o = SingleFlexRig . fmap (composeFlexRig $ () <$ varFlexRig o) . theSingleFlexRig

-- ** Plain free occurrence.

-- | Check if a variable is free, possibly ignoring sorts.
freeIn' :: Free a => IgnoreSorts -> Nat -> a -> Bool
freeIn' ig x t = getAny $ runFree (Any . (x ==)) ig t

{-# SPECIALIZE freeIn :: Nat -> Term -> Bool #-}
freeIn :: Free a => Nat -> a -> Bool
freeIn = freeIn' IgnoreNot

freeInIgnoringSorts :: Free a => Nat -> a -> Bool
freeInIgnoringSorts = freeIn' IgnoreAll

-- UNUSED Liang-Ting Chen 2019-07-16
--freeInIgnoringSortAnn :: Free a => Nat -> a -> Bool
--freeInIgnoringSortAnn = freeIn' IgnoreInAnnotations

-- | Is the variable bound by the abstraction actually used?
isBinderUsed :: Free a => Abs a -> Bool
isBinderUsed NoAbs{}   = False
isBinderUsed (Abs _ x) = 0 `freeIn` x

-- ** Relevant free occurrence.

newtype RelevantIn c = RelevantIn {getRelevantIn :: c}
  deriving (Semigroup, Monoid)

instance IsVarSet a c => IsVarSet a (RelevantIn c) where  -- UndecidableInstances
  withVarOcc o x
    | isIrrelevant o = mempty
    | otherwise = RelevantIn $ withVarOcc o $ getRelevantIn x

relevantIn' :: Free t => IgnoreSorts -> Nat -> t -> Bool
relevantIn' ig x t = getAny . getRelevantIn $ runFree (RelevantIn . Any . (x ==)) ig t

relevantInIgnoringSortAnn :: Free t => Nat -> t -> Bool
relevantInIgnoringSortAnn = relevantIn' IgnoreInAnnotations

relevantIn :: Free t => Nat -> t -> Bool
relevantIn = relevantIn' IgnoreAll

---------------------------------------------------------------------------
-- * Occurrences of all free variables.

-- | Is the term entirely closed (no free variables)?
closed :: Free t => t -> Bool
closed t = getAll $ runFree (const $ All False) IgnoreNot t

-- | Collect all free variables.
allFreeVars :: Free t => t -> VarSet
allFreeVars = runFree IntSet.singleton IgnoreNot

-- | Collect all relevant free variables, possibly ignoring sorts.
allRelevantVarsIgnoring :: Free t => IgnoreSorts -> t -> VarSet
allRelevantVarsIgnoring ig = getRelevantIn . runFree (RelevantIn . IntSet.singleton) ig

-- | Collect all relevant free variables, excluding the "unused" ones.
allRelevantVars :: Free t => t -> VarSet
allRelevantVars = allRelevantVarsIgnoring IgnoreNot

---------------------------------------------------------------------------
-- * Backwards-compatible interface to 'freeVars'.

filterVarMap :: (VarOcc -> Bool) -> VarMap -> VarSet
filterVarMap f = IntMap.keysSet . IntMap.filter f . theVarMap

filterVarMapToList :: (VarOcc -> Bool) -> VarMap -> [Variable]
filterVarMapToList f = map fst . filter (f . snd) . IntMap.toList . theVarMap

-- | Variables under only and at least one inductive constructor(s).
stronglyRigidVars :: VarMap -> VarSet
stronglyRigidVars = filterVarMap $ \case
  VarOcc StronglyRigid _ -> True
  _ -> False

-- | Variables at top or only under inductive record constructors
--   λs and Πs.
--   The purpose of recording these separately is that they
--   can still become strongly rigid if put under a constructor
--   whereas weakly rigid ones stay weakly rigid.
unguardedVars :: VarMap -> VarSet
unguardedVars = filterVarMap $ \case
  VarOcc Unguarded _ -> True
  _ -> False

-- UNUSED Liang-Ting Chen 2019-07-16
---- | Ordinary rigid variables, e.g., in arguments of variables or functions.
--weaklyRigidVars :: VarMap -> VarSet
--weaklyRigidVars = filterVarMap $ \case
--  VarOcc WeaklyRigid _ -> True
--  _ -> False

-- | Rigid variables: either strongly rigid, unguarded, or weakly rigid.
rigidVars :: VarMap -> VarSet
rigidVars = filterVarMap $ \case
  VarOcc o _ -> o `elem` [ WeaklyRigid, Unguarded, StronglyRigid ]

-- UNUSED Liang-Ting Chen 2019-07-16
-- | Variables occuring in arguments of metas.
--   These are only potentially free, depending how the meta variable is instantiated.
--   The set contains the id's of the meta variables that this variable is an argument to.
--flexibleVars :: VarMap -> IntMap MetaSet
--flexibleVars (VarMap m) = (`IntMap.mapMaybe` m) $ \case
--  VarOcc (Flexible ms) _ -> Just ms
--  _ -> Nothing
--
---- | Variables in irrelevant arguments and under a @DontCare@, i.e.,
----   in irrelevant positions.
--irrelevantVars :: VarMap -> VarSet
--irrelevantVars = filterVarMap isIrrelevant

allVars :: VarMap -> VarSet
allVars = IntMap.keysSet . theVarMap
