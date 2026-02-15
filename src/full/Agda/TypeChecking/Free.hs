{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -ddump-simpl -ddump-to-file -dsuppress-all -dno-suppress-type-signatures -dno-typeable-binds #-}

{- |
Computing the free variables of a term.

The distinction between rigid and strongly rigid occurrences comes from: Jason C. Reed, PhD thesis,
2009, page 96 (see also his LFMTP 2009 paper)

The main idea is that x = t(x) is unsolvable if x occurs strongly rigidly in t. It might have a
solution if the occurrence is not strongly rigid, e.g.

  x = \f -> suc (f (x (\ y -> k)))  has  x = \f -> suc (f (suc k))

[Jason C. Reed, PhD thesis, page 106]

The most general function here is 'freeVarMap', which returns returns occurrence information about
every free variable. It is also a legacy function in the sense that it used to be the only function
for computing free occurrences, and it came with various functions for taking views of the resulting
'VarMap'. You can find these under the "Legacy API" here.

There are also also a bunch of specialized and optimized implementations of traversals here.

If you want to write a new function for computing free occurrence information, your task is
essentially to write a 'ComputeFree' instance and invoke 'freeVars'. These together implement a
generic traversal which has a good chance of being converted to decent code by GHC. You can look at
examples here and also look at the comments at 'ComputeFree'.
-}

module Agda.TypeChecking.Free
    (
      FlexRig
    , FlexRig'(..)
    , Free(..)
    , FreeEnv
    , FreeEnv'(..)
    , IgnoreSorts(..)
    , IsVarSet(..)
    , LensFlexRig(..)
    , VarCounts(..)
    , VarMap
    , VarMap'(..)
    , VarOcc
    , VarOcc'(..)
    , composeFlexRig
    , lookupVarMap
    , mapVarMap

    -- * Legacy API
    , allVars
    , filterVarMap
    , filterVarMapToList
    , flexibleVars
    , freeVarMap
    , isFlexible
    , isStronglyRigid
    , isUnguarded
    , isWeaklyRigid
    , rigidVars
    , stronglyRigidVars
    , unguardedVars

    -- * MetaSet
    , MetaSet(..)
    , foldrMetaSet
    , insertMetaSet
    , metaSetToBlocker

    -- * Specialized traversals
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
    , freeVarMapIgnoreAnn
    , freeVarSet
    , isBinderUsed
    , relevantInIgnoringSortAnn
    , setRelInIgnoring
    ) where

import Prelude hiding (null)
import GHC.Exts (Int(..), Int#, (-#), oneShot)

import Data.Semigroup (Any(..), All(..))
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Agda.Syntax.Common hiding (Arg, NamedArg)
import Agda.Syntax.Internal

import Agda.TypeChecking.Free.Base
import Agda.TypeChecking.Free.Generic

import Agda.Utils.VarSet (VarSet)
import Agda.Utils.VarSet qualified as VarSet
import Agda.Utils.StrictReader
import Agda.Utils.StrictFlipEndo
import Agda.Utils.StrictEndo qualified as NonFlip
import Agda.Utils.ExpandCase

-- ** All free variables together with information about their occurrence.
--------------------------------------------------------------------------------

data FreeVarMap = FreeVarMap !Int {-# UNPACK #-} !VarOcc

instance LensFlexRig FreeVarMap MetaSet where
  {-# INLINE lensFlexRig #-}
  lensFlexRig f (FreeVarMap x occ) = FreeVarMap x <$> lensFlexRig f occ

instance LensModality FreeVarMap where
  {-# INLINE getModality #-}
  getModality (FreeVarMap _ occ) = getModality occ
  {-# INLINE mapModality #-}
  mapModality f (FreeVarMap x occ) = FreeVarMap x (mapModality f occ)

instance LensRelevance FreeVarMap

instance ComputeFree FreeVarMap where
  type Collect FreeVarMap = Endo (IntMap VarOcc)
  {-# INLINE underBinders' #-}
  underBinders' n (FreeVarMap x occ) = FreeVarMap (n + x) occ
  {-# INLINE variable' #-}
  variable' x' (FreeVarMap x occ) = Endo \vars ->
    if x' < x then vars
              else IntMap.insertWith (<>) (x' - x) occ vars
  underConstructor' = defaultUnderConstructor; {-# INLINE underConstructor' #-}
  underFlexRig'     = defaultUnderFlexRig;     {-# INLINE underFlexRig' #-}
  underModality'    = defaultUnderModality;    {-# INLINE underModality' #-}
  underRelevance'   = defaultUnderRelevance;   {-# INLINE underRelevance' #-}

{-# SPECIALIZE freeVarMap :: Term -> VarMap #-}
{-# SPECIALIZE freeVarMap :: Type -> VarMap #-}
-- | Return information about every free variable.
freeVarMap :: Free t => t -> VarMap
freeVarMap t =
  VarMap (appEndo (runReader (freeVars t) (FreeVarMap 0 oneVarOcc)) mempty)

--------------------------------------------------------------------------------

newtype FreeVarMapIgnoreAnn = FreeVarMapIgnoreAnn FreeVarMap
  deriving LensModality

instance LensFlexRig FreeVarMapIgnoreAnn MetaSet where
  {-# INLINE lensFlexRig #-}
  lensFlexRig f (FreeVarMapIgnoreAnn x) = FreeVarMapIgnoreAnn <$> lensFlexRig f x

instance LensRelevance FreeVarMapIgnoreAnn

instance ComputeFree FreeVarMapIgnoreAnn where
  type Collect FreeVarMapIgnoreAnn = Endo (IntMap VarOcc)
  {-# INLINE underBinders' #-}
  underBinders' n (FreeVarMapIgnoreAnn x) = FreeVarMapIgnoreAnn (underBinders' n x)
  {-# INLINE variable' #-}
  variable' x' (FreeVarMapIgnoreAnn x) = variable' x' x
  ignoreSorts'      = IgnoreInAnnotations;     {-# INLINE ignoreSorts' #-}
  underConstructor' = defaultUnderConstructor; {-# INLINE underConstructor' #-}
  underFlexRig'     = defaultUnderFlexRig;     {-# INLINE underFlexRig' #-}
  underModality'    = defaultUnderModality;    {-# INLINE underModality' #-}
  underRelevance'   = defaultUnderRelevance;   {-# INLINE underRelevance' #-}

{-# SPECIALIZE freeVarMapIgnoreAnn :: Term -> VarMap #-}
{-# SPECIALIZE freeVarMapIgnoreAnn :: (Term,Type) -> VarMap #-}
-- | Return information about every free variable, but ignore occurrences
--   in sorts of types.
freeVarMapIgnoreAnn :: Free t => t -> VarMap
freeVarMapIgnoreAnn t =
  VarMap (appEndo (runReader (freeVars t)
                  (FreeVarMapIgnoreAnn (FreeVarMap 0 oneVarOcc))) mempty)

--------------------------------------------------------------------------------

newtype FreeVarCounts = FreeVarCounts Int

instance ComputeFree FreeVarCounts where
  type Collect FreeVarCounts = Endo (IntMap Int)
  {-# INLINE underBinders' #-}
  underBinders' n (FreeVarCounts x) = FreeVarCounts (n + x)
  {-# INLINE variable' #-}
  variable' x' (FreeVarCounts x) = Endo \counts ->
    if x' < x then counts else IntMap.insertWith (+) (x' - x) 1 counts

{-# SPECIALIZE freeVarCounts :: Term -> VarCounts #-}
-- | Return how many times each free variable occurs.
freeVarCounts :: Free t => t -> VarCounts
freeVarCounts t =
  VarCounts (appEndo (runReader (freeVars t) (FreeVarCounts 0)) mempty)

-- ** Testing that a predicate holds on any free variable
--------------------------------------------------------------------------------

data AnyFreeVar = AnyFreeVar !Int !(Int# -> Bool)

instance ComputeFree AnyFreeVar where
  type Collect AnyFreeVar = Any
  {-# INLINE underBinders' #-}
  underBinders' n (AnyFreeVar x f) = AnyFreeVar (n + x) f
  {-# INLINE variable' #-}
  variable' (I# x') (AnyFreeVar (I# x) f) = if I# x' < I# x then mempty else Any (f (x' -# x))

{-# SPECIALIZE anyFreeVar# :: (Int# -> Bool) -> Dom' Term Type -> Bool #-}
anyFreeVar# :: Free t => (Int# -> Bool) -> t -> Bool
anyFreeVar# f t = getAny (runReader (freeVars t) (AnyFreeVar 0 f))

{-# INLINE anyFreeVar #-}
-- | Compute the disjunction of a predicate on free variables.
anyFreeVar :: Free t => (Int -> Bool) -> t -> Bool
anyFreeVar f = anyFreeVar# (\n -> f (I# n))

{-# SPECIALIZE allFreeVar# :: (Int# -> Bool) -> Dom' Term Type -> Bool #-}
allFreeVar# :: Free t => (Int# -> Bool) -> t -> Bool
allFreeVar# f t = not (getAny (runReader (freeVars t) (AnyFreeVar 0 (\n -> not (f n)))))

{-# INLINE allFreeVar #-}
-- | Compute the conjunction of a predicate on free variables.
allFreeVar :: Free t => (Int -> Bool) -> t -> Bool
allFreeVar f = allFreeVar# (\n -> f (I# n))

data AnyFreeVarIgnoreAll = AnyFreeVarIgnoreAll !Int !(Int# -> Bool)

instance ComputeFree AnyFreeVarIgnoreAll where
  type Collect AnyFreeVarIgnoreAll = Any
  {-# INLINE underBinders' #-}
  underBinders' n (AnyFreeVarIgnoreAll x f) = AnyFreeVarIgnoreAll (n + x) f
  {-# INLINE variable' #-}
  variable' (I# x') (AnyFreeVarIgnoreAll (I# x) f) =
    if I# x' < I# x then mempty else Any (f (x' -# x))
  {-# INLINE ignoreSorts' #-}
  ignoreSorts' = IgnoreAll

{-# SPECIALIZE anyFreeVarIgnoreAll# :: (Int# -> Bool) -> Term -> Bool #-}
anyFreeVarIgnoreAll# :: Free t => (Int# -> Bool) -> t -> Bool
anyFreeVarIgnoreAll# f t = getAny (runReader (freeVars t) (AnyFreeVarIgnoreAll 0 f))

{-# INLINE anyFreeVarIgnoreAll #-}
-- | Same as 'anyFreeVar' except occurrences in sorts of types are ignored.
anyFreeVarIgnoreAll :: (Int -> Bool) -> Term -> Bool
anyFreeVarIgnoreAll f = anyFreeVarIgnoreAll# (\n -> f (I# n))

-- SPECIALIZED to TCM.Constraint in SizedTypes.Solve
allFreeVarIgnoreAll# :: Free t => (Int# -> Bool) -> t -> Bool
allFreeVarIgnoreAll# f t =
  not (getAny (runReader (freeVars t) (AnyFreeVarIgnoreAll 0 (\n -> not (f n)))))

{-# INLINE allFreeVarIgnoreAll #-}
-- | Same as 'allFreeVar' except occurrences in sorts of types are ignored.
allFreeVarIgnoreAll :: Free t => (Int -> Bool) -> t -> Bool
allFreeVarIgnoreAll f = allFreeVarIgnoreAll# (\n -> f (I# n))

-- ** Flex-rigid occurrence for a single variable
--------------------------------------------------------------------------------

data SingleFR = SingleFR !Int !FlexRig

instance LensFlexRig SingleFR MetaSet where
  {-# INLINE lensFlexRig #-}
  lensFlexRig f (SingleFR x fr) = SingleFR x <$> f fr

data CollectSingleFR = CSFRNothing | CSFRJust !FlexRig

instance Semigroup CollectSingleFR where
  CSFRJust fr <> CSFRJust fr' = CSFRJust (addFlexRig fr fr')
  CSFRNothing <> s            = s
  s           <> CSFRNothing  = s

instance ComputeFree SingleFR where
  type Collect SingleFR = Endo CollectSingleFR
  {-# INLINE underBinders' #-}
  underBinders' n (SingleFR x fr) = SingleFR (n + x) fr
  {-# INLINE variable' #-}
  variable' x' (SingleFR x fr) = Endo \acc -> if x == x' then acc <> CSFRJust fr else acc
  underConstructor' = defaultUnderConstructor; {-# INLINE underConstructor' #-}
  underFlexRig'     = defaultUnderFlexRig; {-# INLINE underFlexRig' #-}

{-# SPECIALIZE flexRigOccurrenceIn :: Nat -> Term -> Maybe FlexRig #-}
{-# SPECIALIZE flexRigOccurrenceIn :: Nat -> Sort' Term -> Maybe FlexRig #-}
-- | Compute 'FlexRig' for a single variable.
flexRigOccurrenceIn :: Free a => Nat -> a -> Maybe FlexRig
flexRigOccurrenceIn x a = case appEndo (runReader (freeVars a) (SingleFR x Unguarded)) CSFRNothing of
  CSFRNothing -> Nothing
  CSFRJust fr -> Just fr

-- ** Plain free occurrence
--------------------------------------------------------------------------------

newtype FreeIn = FreeIn Int

instance ComputeFree FreeIn where
  type Collect FreeIn = Any
  underBinders' n (FreeIn x) = FreeIn (n + x); {-# INLINE underBinders' #-}
  variable' x' (FreeIn x) = Any (x == x'); {-# INLINE variable' #-}

{-# SPECIALIZE freeIn :: Nat -> Term -> Bool #-}
{-# SPECIALIZE freeIn :: Nat -> Type -> Bool #-}
-- | Check if single variable occurs freely.
freeIn :: Free t => Nat -> t -> Bool
freeIn x a = getAny (runReader (freeVars a) (FreeIn x))

newtype FreeInIgnoringSorts = FreeInIgnoringSorts Int

instance ComputeFree FreeInIgnoringSorts where
  type Collect FreeInIgnoringSorts = Any
  underBinders' n (FreeInIgnoringSorts x) = FreeInIgnoringSorts (n + x); {-# INLINE underBinders' #-}
  variable' x' (FreeInIgnoringSorts x) = Any (x == x'); {-# INLINE variable' #-}
  ignoreSorts' = IgnoreAll; {-# INLINE ignoreSorts' #-}

{-# SPECIALIZE freeInIgnoringSorts :: Nat -> Term -> Bool #-}
{-# SPECIALIZE freeInIgnoringSorts :: Nat -> Type -> Bool #-}
-- | Check if a single variable occurs freely outside of sorts of types.
freeInIgnoringSorts :: Free a => Nat -> a -> Bool
freeInIgnoringSorts x a = getAny (runReader (freeVars a) (FreeInIgnoringSorts x))

{-# INLINE isBinderUsed #-}
-- | Is the variable bound by the abstraction actually used?
isBinderUsed :: Free a => Abs a -> Bool
isBinderUsed NoAbs{}   = False
isBinderUsed (Abs _ x) = 0 `freeIn` x

-- ** Relevant free occurrence.
--------------------------------------------------------------------------------

data RelevantInIgnoringSortAnn = RelevantInIgnoringSortAnn !Int !Relevance

instance LensRelevance RelevantInIgnoringSortAnn where
  getRelevance (RelevantInIgnoringSortAnn _ r) = r
  mapRelevance f (RelevantInIgnoringSortAnn x r) = RelevantInIgnoringSortAnn x (f r)

instance ComputeFree RelevantInIgnoringSortAnn where
  type Collect RelevantInIgnoringSortAnn = Any
  {-# INLINE underBinders' #-}
  underBinders' n (RelevantInIgnoringSortAnn x r) =
    RelevantInIgnoringSortAnn (n + x) r
  {-# INLINE variable' #-}
  variable' x' (RelevantInIgnoringSortAnn x r) = Any (x' == x && not (isIrrelevant r))
  ignoreSorts' = IgnoreInAnnotations; {-# INLINE ignoreSorts' #-}
  {-# INLINE underModality' #-}
  underModality' = Just \m (RelevantInIgnoringSortAnn x r) ->
    RelevantInIgnoringSortAnn x (composeRelevance (getRelevance m) r)
  underRelevance' = defaultUnderRelevance;   {-# INLINE underRelevance' #-}

{-# SPECIALIZE relevantInIgnoringSortAnn :: Nat -> Term -> Bool #-}
{-# SPECIALIZE relevantInIgnoringSortAnn :: Nat -> Type -> Bool #-}
{-# SPECIALIZE relevantInIgnoringSortAnn :: Nat -> Dom' Term Type -> Bool #-}
-- | Does a variable occur relevantly and outside of sorts of types?
relevantInIgnoringSortAnn :: Free t => Nat -> t -> Bool
relevantInIgnoringSortAnn x t =
  getAny (runReader (freeVars t) (RelevantInIgnoringSortAnn x unitRelevance))

-- ** Closed objects
---------------------------------------------------------------------------

newtype Closed = Closed Int -- ^ Local scope size.

instance ComputeFree Closed where
  type Collect Closed = All
  underBinders' n (Closed x) = Closed (n + x); {-# INLINE underBinders' #-}
  variable' x' (Closed x) = All (x' < x); {-# INLINE variable' #-}

{-# SPECIALIZE closed :: Term -> Bool #-}
{-# SPECIALIZE closed :: Dom' Term Type -> Bool #-}
-- | Is a term closed?
closed :: Free t => t -> Bool
closed t = getAll (runReader (freeVars t) (Closed 0))

-- ** Test free occurrence for a set of variables
--------------------------------------------------------------------------------

data SetRelInIgnoring = SetRelInIgnoring !Int !Relevance

instance LensRelevance SetRelInIgnoring where
  getRelevance (SetRelInIgnoring _ r) = r
  mapRelevance f (SetRelInIgnoring x r) = SetRelInIgnoring x (f r)

newtype CollectSFII = CollectSFII {appCSFII :: VarSet -> VarSet}

instance Semigroup CollectSFII where
  {-# INLINE (<>) #-}
  CollectSFII f <> CollectSFII g = CollectSFII (oneShot \xs -> case f xs of
    xs -> if VarSet.null xs then xs else g xs)

instance Monoid CollectSFII where
  {-# INLINE mempty #-}
  mempty = CollectSFII \xs -> xs

instance ExpandCase CollectSFII where
  type Result CollectSFII = VarSet
  {-# INLINE expand #-}
  expand k = CollectSFII (oneShot \a -> k (oneShot \act -> appCSFII act a))

instance ComputeFree SetRelInIgnoring where
  type Collect SetRelInIgnoring = CollectSFII
  {-# INLINE underBinders' #-}
  underBinders' n (SetRelInIgnoring x r) = SetRelInIgnoring (n + x) r
  {-# INLINE variable' #-}
  variable' x' (SetRelInIgnoring x r) = CollectSFII \xs ->
    if x' >= x && not (isIrrelevant r)
      then VarSet.delete (x' - x) xs
      else xs
  ignoreSorts' = IgnoreInAnnotations; {-# INLINE ignoreSorts' #-}
  underModality' = Just \m (SetRelInIgnoring x r) ->
    SetRelInIgnoring x (composeRelevance (getRelevance m) r)
  underRelevance' = defaultUnderRelevance;   {-# INLINE underRelevance' #-}

{-# SPECIALIZE NOINLINE setRelInIgnoring :: VarSet -> Dom Type -> VarSet #-}
{-# SPECIALIZE NOINLINE setRelInIgnoring :: VarSet -> Type -> VarSet #-}
-- | Test for a set of variables whether each variable occurs relevantly and outside of sort annotations.
--   Return the set of variables that __don't__ occur.
setRelInIgnoring :: Free t => VarSet -> t -> VarSet
setRelInIgnoring xs t
  | VarSet.null xs = xs
  | otherwise      = appCSFII (runReader (freeVars t) (SetRelInIgnoring 0 unitRelevance)) xs


-- ** Collect free variables
--------------------------------------------------------------------------------

newtype FreeVarSet = FreeVarSet Int

instance ComputeFree FreeVarSet where
  type Collect FreeVarSet = Endo VarSet
  {-# INLINE underBinders' #-}
  underBinders' n (FreeVarSet x) = FreeVarSet (n + x)
  {-# INLINE variable' #-}
  variable' x' (FreeVarSet x) = Endo \xs -> if x' < x then xs else VarSet.insert (x' - x) xs

{-# SPECIALIZE freeVarSet :: Term -> VarSet #-}
{-# SPECIALIZE freeVarSet :: Dom' Term Type -> VarSet #-}
-- | Compute the set of free variables.
freeVarSet :: Free t => t -> VarSet
freeVarSet t = appEndo (runReader (freeVars t) (FreeVarSet 0)) mempty

newtype FreeVarList = FreeVarList Int

instance ComputeFree FreeVarList where
  -- Need the non-flipped endo to get left-right element order
  type Collect FreeVarList = NonFlip.Endo [Int]
  {-# INLINE underBinders' #-}
  underBinders' n (FreeVarList x) = FreeVarList (n + x)
  {-# INLINE variable' #-}
  variable' x' (FreeVarList x) = NonFlip.Endo \xs ->
    if x' < x then xs else let !v = x' - x in v : xs

{-# SPECIALIZE freeVarList :: Term -> [Int] #-}
{-# SPECIALIZE freeVarList :: Maybe Term -> [Int] #-}
-- | Compute a (possibly non-unique) list of free variables, in preorder traversal order.
freeVarList :: Free t => t -> [Int]
freeVarList t = NonFlip.appEndo (runReader (freeVars t) (FreeVarList 0)) []

-- ** Backwards-compatible interface, for extracting information from a 'VarMap'.
---------------------------------------------------------------------------

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
