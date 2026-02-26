{-# LANGUAGE CPP #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE MagicHash #-}
{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}

#if  __GLASGOW_HASKELL__ > 902
{-# OPTIONS_GHC -fworker-wrapper-cbv #-}
#endif

-- | Free variable check that reduces the subject to make certain variables not
--   free. Used when pruning metavariables in Agda.TypeChecking.MetaVars.Occurs.
module Agda.TypeChecking.Free.Reduce
  ( ForceNotFree
  , forceNotFree
  , forceNoAbs
  , forceNoAbsSort
  , reallyFree
  , IsFree(..)
  , nonFreeVars
  ) where

import Prelude hiding (null)

import Data.Maybe
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)
import GHC.Exts

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Base (constructorFlexRig, addFlexRig, oneFlexRig)
import Agda.TypeChecking.Free.Precompute

import qualified Agda.Utils.VarSet as VarSet
import Agda.Utils.VarSet (VarSet)
import Agda.Utils.StrictState
import Agda.Utils.StrictReader
import Agda.Utils.ExpandCase
import Agda.Utils.Singleton
import Agda.Utils.Impossible


-- | A variable can either not occur (`NotFree`) or it does occur
--   (`MaybeFree`).  In the latter case, the occurrence may disappear
--   depending on the instantiation of some set of metas.
data IsFree
  = MaybeFree FlexRig
  | NotFree
  deriving (Eq, Show)

-- local scope size, VarSet to enforce not occurring, FlexRig we're under, ReduceEnv
-- András, 2026-02-12: the ReduceEnv is put in the FREnv because I don't want to bother
-- fixing GHC code generation (i.e. not returning closures from case splits) for ReduceM.
data FREnv = FREnv Int VarSet FlexRig ReduceEnv

-- This is equivalent to IntMap IsFree, where the NotFree cases are factored out into
-- a VarSet for efficiency.
data FRState = FRState VarSet (IntMap FlexRig)
type FreeRed = StateT FRState (Reader FREnv)

{-# SPECIALIZE forceNotFree :: VarSet -> Term -> ReduceM (IntMap IsFree, Term) #-}
-- | Try to enforce a set of variables not occurring in a given
--   type. Returns a possibly reduced version of the type and for each
--   of the given variables whether it is either not free, or
--   maybe free depending on some metavariables.
forceNotFree :: (ForceNotFree a, Reduce a) => VarSet -> a -> ReduceM (IntMap IsFree, a)
forceNotFree xs a = ReduceM \env ->
  let (a', FRState notfree mxs) =
        runReader (runStateT (forceNotFreeR $ precomputeFreeVars_ a) (FRState xs mempty))
                  (FREnv 0 xs oneFlexRig env) in
  let mxs' = VarSet.foldl' (\k -> IntMap.insert k NotFree) (MaybeFree <$> mxs) notfree in
  (mxs', a')

{-# SPECIALIZE reallyFree :: VarSet -> Term -> ReduceM (Either Blocked_ (Maybe Term)) #-}
-- | Checks if the given term contains any free variables that are in
--   the given set of variables, possibly reducing the term in the
--   process.  Returns `Right Nothing` if there are such variables,
--   `Right (Just v')` if there are none (where v' is the possibly
--   reduced version of the given term) or `Left b` if the problem is
--   blocked on a meta.
reallyFree :: (Reduce a, ForceNotFree a) => VarSet -> a -> ReduceM (Either Blocked_ (Maybe a))
reallyFree xs v = do
  (mxs , v') <- forceNotFree xs v
  case IntMap.foldr pickFree NotFree mxs of
    MaybeFree (Flexible ms) -> do
      let !blocker = metaSetToBlocker ms
      pure $ Left $ Blocked blocker ()
    MaybeFree _ -> pure $ Right Nothing
    NotFree     -> pure $ Right (Just v')
  where
    -- Check if any of the variables occur freely.
    pickFree :: IsFree -> IsFree -> IsFree
    pickFree (MaybeFree ms1) (MaybeFree ms2) = MaybeFree $! (ms1 `addFlexRig` ms2)
    pickFree f1 NotFree = f1
    pickFree NotFree f2 = f2

-- | Try to force a binder to be a NoAbs by reducing the body as needed
--   to get rid of the bound variable. Returns either the reduced abstraction
--   and the occurrence of the variable (if removing it failed) or else
--   the strengthened body.
forceNoAbs :: (Reduce a, ForceNotFree a)
           => Dom Type -> Abs a -> ReduceM (Either (Abs a, FlexRig) a)
forceNoAbs dom (NoAbs _ x) = pure $ Right x
forceNoAbs dom (Abs n x)   = underAbsReduceM dom (Abs n x) \x -> do
  (fvm, x) <- forceNotFree (singleton 0) x
  case fromMaybe __IMPOSSIBLE__ (IntMap.lookup 0 fvm) of
    NotFree           -> pure $! Right $! noabsApp __IMPOSSIBLE__ (Abs n x)
    MaybeFree flexRig -> pure $ Left (Abs n x , flexRig)

-- | András 2026-02-24: we specialize this, because TypeChecking.Reduce imports it via the hs-boot
--   file, and if it's not specialized there, it is __impossible__ to specialzie by GHC.
forceNoAbsSort :: Dom Type -> Abs Sort -> ReduceM (Either (Abs Sort, FlexRig) Sort)
forceNoAbsSort = forceNoAbs

-- | Get the set of 'NotFree' variables from a variable map.
nonFreeVars :: IntMap IsFree -> VarSet
nonFreeVars =
  IntMap.foldlWithKey'
    (\acc k v -> case v of
        NotFree -> VarSet.insert k acc
        _       -> acc)
    mempty


class (PrecomputeFreeVars a, Subst a) => ForceNotFree a where
  -- Reduce the argument if necessary, to make as many as possible of
  -- the variables in the state not free. Updates the state, marking
  -- the variables that couldn't be make not free as `MaybeFree`. By
  -- updating the state as soon as a variable can not be reduced away,
  -- we avoid trying to get rid of it in other places.
  forceNotFree' :: a -> FreeRed a

{-# NOINLINE notFreeInPrecomputedSlow #-}
notFreeInPrecomputedSlow :: Int# -> VarSet -> VarSet -> Bool
notFreeInPrecomputedSlow locals xs precomp =
  VarSet.disjoint xs (VarSet.strengthen (I# locals) precomp)

{-# INLINE noFreeInPrecomputed #-}
noFreeInPrecomputed :: Int -> VarSet -> VarSet -> Bool
noFreeInPrecomputed (I# locals) xs precomp = case (xs, precomp) of
  -- fast path
  (VarSet.VS# xs, VarSet.VS# precomp) ->
    isTrue# ((xs `and#` (precomp `shiftRL#` locals)) `eqWord#` 0##)
  -- rare slow path
  _ -> notFreeInPrecomputedSlow locals xs precomp

{-# INLINE reduceIfFreeVars #-}
-- Reduce the argument if there are offending free variables. Doesn't call the
-- continuation when no reduction is required.
reduceIfFreeVars :: (Reduce a, ForceNotFree a) => (a -> FreeRed a) -> a -> FreeRed a
reduceIfFreeVars k = \a -> do
  FRState notfrees _ <- get
  FREnv locals _ _ env <- ask
  let fvs = precomputedFreeVars a
  if noFreeInPrecomputed locals notfrees fvs
    then pure a
    else k $ precomputeFreeVars_ (unReduceM (reduce a) env)

-- Careful not to define forceNotFree' = forceNotFreeR since that would loop.
forceNotFreeR :: (Reduce a, ForceNotFree a) => a -> FreeRed a
forceNotFreeR = reduceIfFreeVars forceNotFree'

{-# INLINE underFlexRig #-}
underFlexRig :: FlexRig -> FreeRed a -> FreeRed a
underFlexRig fr' = local \(FREnv x nfs fr e) -> FREnv x nfs (composeFlexRig fr' fr) e

{-# INLINE underConstructor #-}
underConstructor :: ConHead -> Elims -> FreeRed a -> FreeRed a
underConstructor c es = underFlexRig (constructorFlexRig c es)

instance (Reduce a, ForceNotFree a) => ForceNotFree (Arg a) where
  -- Precomputed free variables are stored in the Arg so reduceIf outside the
  -- traverse.
  forceNotFree' = reduceIfFreeVars (traverse forceNotFree')

instance (Reduce a, ForceNotFree a, TermSubst a) => ForceNotFree (Dom a) where
  forceNotFree' = traverse forceNotFreeR

instance (Reduce a, ForceNotFree a) => ForceNotFree (Abs a) where
  -- Reduction stops at abstractions (lambda/pi) so do reduceIf/forceNotFreeR here.
  forceNotFree' abs = expand \ret -> case abs of
    a@NoAbs{}   -> ret $ traverse forceNotFreeR a
    a@(Abs x _) -> ret do
      let updEnv :: ReduceEnv -> ReduceEnv
          updEnv e = extendReduceEnv x __DUMMY_DOM__ e
      reduceIfFreeVars
        (local (\(FREnv x nfs fr e) -> FREnv (x + 1) nfs fr (updEnv e)) . traverse forceNotFree')
        a

instance ForceNotFree a => ForceNotFree [a] where
  forceNotFree' as = expand \ret -> case as of
    []     -> ret $ pure []
    (a:as) -> ret $ (:) <$> forceNotFree' a <*> forceNotFree' as

instance (Reduce a, ForceNotFree a) => ForceNotFree (Elim' a) where
  -- There's an Arg inside Elim' which stores precomputed free vars, so let's
  -- not skip over that.
  forceNotFree' e = expand \ret -> case e of
    Apply arg    -> ret $ Apply <$> forceNotFree' arg
    e@Proj{}     -> ret $ pure e
    IApply x y r -> ret $ IApply <$> forceNotFreeR x <*> forceNotFreeR y <*> forceNotFreeR r

instance ForceNotFree Type where
  forceNotFree' a = expand \ret -> case a of
    El s t -> ret $ El <$> forceNotFree' s <*> forceNotFree' t

instance ForceNotFree Term where
  forceNotFree' t = expand \ret -> case t of
    Var x es -> ret do
      FREnv locals wantToNotFree fr _ <- ask
      FRState xs frs <- get
      let x' = x - locals
      expand \ret -> if (x >= locals && VarSet.member x' wantToNotFree) then ret do
        put $! FRState (VarSet.delete x' xs) (IntMap.insert x' fr frs)
        Var x <$> underFlexRig WeaklyRigid (forceNotFree' es)
      else ret do
        Var x <$> underFlexRig WeaklyRigid (forceNotFree' es)
    Def f es   -> ret $ Def f    <$> underFlexRig WeaklyRigid (forceNotFree' es)
    Con c h es -> ret $ Con c h  <$> underConstructor c es (forceNotFree' es)
    MetaV m es -> ret $ MetaV m  <$> underFlexRig (Flexible (singleton m)) (forceNotFree' es)
    Lam h b    -> ret $ Lam h    <$> underFlexRig WeaklyRigid (forceNotFree' b)
    Pi a b     -> ret $ Pi       <$> forceNotFree' a <*> forceNotFree' b  -- Dom and Abs do reduceIf so not needed here
    Sort s     -> ret $ Sort     <$> forceNotFree' s
    Level l    -> ret $ Level    <$> forceNotFree' l
    DontCare t -> ret $ DontCare <$> forceNotFreeR t  -- Reduction stops at DontCare so reduceIf
    t@Lit{}    -> ret $ pure t
    t@Dummy{}  -> ret $ pure t

instance ForceNotFree Level where
  {-# INLINE forceNotFree' #-}
  forceNotFree' (Max m as) = Max m <$> forceNotFree' as

instance ForceNotFree PlusLevel where
  {-# INLINE forceNotFree' #-}
  forceNotFree' (Plus k a) = Plus k <$> forceNotFree' a

instance ForceNotFree Sort where
  -- Reduce for sorts already goes under all sort constructors, so we can get
  -- away without forceNotFreeR here.
  forceNotFree' s = expand \ret -> case s of
    Univ u l       -> ret $ Univ u <$> forceNotFree' l
    PiSort a b c   -> ret do a        <- underFlexRig (Flexible mempty) (forceNotFree' a)
                             (!b, !c) <- underFlexRig WeaklyRigid ((,) <$> forceNotFree' b <*> forceNotFree' c)
                             pure $ PiSort a b c
    FunSort a b    -> ret $ FunSort <$> forceNotFree' a <*> forceNotFree' b
    UnivSort s     -> ret $ UnivSort <$> underFlexRig WeaklyRigid (forceNotFree' s)
    MetaS x es     -> ret $ MetaS x <$> underFlexRig (Flexible (singleton x)) (forceNotFree' es)
    DefS d es      -> ret $ DefS d <$> underFlexRig WeaklyRigid (forceNotFree' es)
    s@(Inf _ _)    -> ret $ pure s
    s@SizeUniv     -> ret $ pure s
    s@LockUniv     -> ret $ pure s
    s@LevelUniv    -> ret $ pure s
    s@IntervalUniv -> ret $ pure s
    s@DummyS{}     -> ret $ pure s
