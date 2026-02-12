{-# LANGUAGE MagicHash, UnboxedSums, UnboxedTuples, CPP #-}
{-# OPTIONS_GHC -ddump-simpl -dsuppress-all -dno-suppress-type-signatures -ddump-to-file -dno-typeable-binds #-}

#if  __GLASGOW_HASKELL__ > 902
{-# OPTIONS_GHC -fworker-wrapper-cbv -fmax-worker-args=12 #-}
#endif

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

import Prelude hiding (null)

import Data.Semigroup ( Any(..), All(..) )
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import GHC.Exts hiding (Any)

import Agda.Benchmarking qualified as Bench

import Agda.Syntax.Common hiding (Arg, NamedArg)
import Agda.Syntax.Internal

import Agda.TypeChecking.Free.Base
import Agda.TypeChecking.Free.LazyNew

import Agda.Utils.VarSet (VarSet)
import Agda.Utils.VarSet qualified as VarSet
import Agda.Utils.Singleton
import Agda.Utils.StrictReader
import Agda.Utils.StrictEndo
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
freeVarCounts :: Free t => t -> VarCounts
freeVarCounts t =
  VarCounts (appEndo (runReader (freeVars t) (FreeVarCounts 0)) mempty)

-- ** Testing that a predicate holds on any free variable
--------------------------------------------------------------------------------

data AnyFreeVar = AnyFreeVar !Int !(Int -> Bool)

instance ComputeFree AnyFreeVar where
  type Collect AnyFreeVar = Any
  {-# INLINE underBinders' #-}
  underBinders' n (AnyFreeVar x f) = AnyFreeVar (n + x) f
  {-# INLINE variable' #-}
  variable' x' (AnyFreeVar x f) = if x' < x then mempty else Any (f (x' - x))

{-# SPECIALIZE anyFreeVar :: (Int -> Bool) -> Term -> Bool #-}
anyFreeVar :: Free t => (Int -> Bool) -> t -> Bool
anyFreeVar f t = getAny (runReader (freeVars t) (AnyFreeVar 0 f))

allFreeVar :: Free t => (Int -> Bool) -> t -> Bool
allFreeVar f t = not (getAny (runReader (freeVars t) (AnyFreeVar 0 (not . f))))

data AnyFreeVarIgnoreAll = AnyFreeVarIgnoreAll !Int !(Int -> Bool)

instance ComputeFree AnyFreeVarIgnoreAll where
  type Collect AnyFreeVarIgnoreAll = Any
  {-# INLINE underBinders' #-}
  underBinders' n (AnyFreeVarIgnoreAll x f) = AnyFreeVarIgnoreAll (n + x) f
  {-# INLINE variable' #-}
  variable' x' (AnyFreeVarIgnoreAll x f) = if x' < x then mempty else Any (f (x' - x))
  {-# INLINE ignoreSorts' #-}
  ignoreSorts' = IgnoreAll

{-# SPECIALIZE anyFreeVarIgnoreAll :: (Int -> Bool) -> Term -> Bool #-}
anyFreeVarIgnoreAll :: Free t => (Int -> Bool) -> t -> Bool
anyFreeVarIgnoreAll f t = getAny (runReader (freeVars t) (AnyFreeVarIgnoreAll 0 f))

allFreeVarIgnoreAll :: Free t => (Int -> Bool) -> t -> Bool
allFreeVarIgnoreAll f t =
  not (getAny (runReader (freeVars t) (AnyFreeVarIgnoreAll 0 (not . f))))


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
flexRigOccurrenceIn :: Free a => Nat -> a -> Maybe FlexRig
flexRigOccurrenceIn x a = case appEndo (runReader (freeVars a) (SingleFR x Unguarded)) CSFRNothing of
  CSFRNothing -> Nothing
  CSFRJust fr -> Just fr

-- ** Plain free occurrence
--------------------------------------------------------------------------------

instance ExpandCase Any where
  type Result Any = Any
  expand k = k id; {-# INLINE expand #-}

newtype FreeIn = FreeIn Int

instance ComputeFree FreeIn where
  type Collect FreeIn = Any
  underBinders' n (FreeIn x) = FreeIn (n + x); {-# INLINE underBinders' #-}
  variable' x' (FreeIn x) = Any (x == x'); {-# INLINE variable' #-}

{-# SPECIALIZE freeIn :: Nat -> Term -> Bool #-}
freeIn :: Free a => Nat -> a -> Bool
freeIn x a = getAny (runReader (freeVars a) (FreeIn x))

newtype FreeInIgnoringSorts = FreeInIgnoringSorts Int

instance ComputeFree FreeInIgnoringSorts where
  type Collect FreeInIgnoringSorts = Any
  underBinders' n (FreeInIgnoringSorts x) = FreeInIgnoringSorts (n + x); {-# INLINE underBinders' #-}
  variable' x' (FreeInIgnoringSorts x) = Any (x == x'); {-# INLINE variable' #-}
  ignoreSorts' = IgnoreAll; {-# INLINE ignoreSorts' #-}

{-# SPECIALIZE freeInIgnoringSorts :: Nat -> Term -> Bool #-}
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
relevantInIgnoringSortAnn :: Free t => Nat -> t -> Bool
relevantInIgnoringSortAnn x t =
  getAny (runReader (freeVars t) (RelevantInIgnoringSortAnn x unitRelevance))

-- ** Closed objects
---------------------------------------------------------------------------

newtype Closed = Closed Int -- ^ Local scope size.

instance ExpandCase All where
  type Result All = All
  expand k = k id; {-# INLINE expand #-}

instance ComputeFree Closed where
  type Collect Closed = All
  underBinders' n (Closed x) = Closed (n + x); {-# INLINE underBinders' #-}
  variable' x' (Closed x) = All (x' < x); {-# INLINE variable' #-}

{-# SPECIALIZE closed :: Term -> Bool #-}
closed :: Free t => t -> Bool
closed t = getAll (runReader (freeVars t) (Closed 0))

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
-- | Collect all free variables.
freeVarSet :: Free t => t -> VarSet
freeVarSet t = appEndo (runReader (freeVars t) (FreeVarSet 0)) mempty

newtype FreeVarList = FreeVarList Int

instance ComputeFree FreeVarList where
  type Collect FreeVarList = Endo [Int]
  {-# INLINE underBinders' #-}
  underBinders' n (FreeVarList x) = FreeVarList (n + x)
  {-# INLINE variable' #-}
  variable' x' (FreeVarList x) = Endo \xs ->
    if x' < x then xs else let !v = x' - x in v : xs

{-# SPECIALIZE freeVarList :: Term -> [Int] #-}
-- | Collect all free variables.
freeVarList :: Free t => t -> [Int]
freeVarList t = appEndo (runReader (freeVars t) (FreeVarList 0)) []
