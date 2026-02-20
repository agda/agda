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
  , reallyFree
  , IsFree(..)
  , nonFreeVars
  ) where

import Prelude hiding (null)

import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)
import GHC.Exts

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Precompute

import Agda.Utils.Null
import qualified Agda.Utils.VarSet as VarSet
import Agda.Utils.VarSet (VarSet)
import Agda.Utils.StrictState
import Agda.Utils.StrictReader


-- | A variable can either not occur (`NotFree`) or it does occur
--   (`MaybeFree`).  In the latter case, the occurrence may disappear
--   depending on the instantiation of some set of metas.
data IsFree
  = MaybeFree MetaSet
  | NotFree
  deriving (Eq, Show)

-- local scope size, VarSet to enforce not occurring, MetaSet we're under, ReduceEnv
-- András, 2026-02-12: the ReduceEnv is put in the FREnv because I don't want to bother
-- fixing GHC code generation (i.e. not returning closures from case splits) for ReduceM.
data FREnv = FREnv Int VarSet MetaSet ReduceEnv

-- This is equivalent to IntMap IsFree, where the NotFree cases are factored out into
-- a VarSet for efficiency.
data FRState = FRState VarSet (IntMap MetaSet)

type FreeRed = ReaderT FREnv (State FRState)

{-# SPECIALIZE forceNotFree :: VarSet -> Term -> ReduceM (IntMap IsFree, Term) #-}
-- | Try to enforce a set of variables not occurring in a given
--   type. Returns a possibly reduced version of the type and for each
--   of the given variables whether it is either not free, or
--   maybe free depending on some metavariables.
forceNotFree :: (ForceNotFree a, Reduce a) => VarSet -> a -> ReduceM (IntMap IsFree, a)
forceNotFree xs a = ReduceM \env ->
  let (a', FRState notfree mxs) =
        runState (runReaderT (forceNotFreeR $ precomputeFreeVars_ a) (FREnv 0 xs mempty env))
                 (FRState xs mempty) in
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
    MaybeFree ms
      | null ms   -> return $ Right Nothing
      | otherwise -> return $ Left $ Blocked blocker ()
      where blocker = metaSetToBlocker ms
    NotFree -> return $ Right (Just v')
  where
    -- Check if any of the variables occur freely.
    -- Prefer occurrences that do not depend on any metas.
    pickFree :: IsFree -> IsFree -> IsFree
    pickFree f1@(MaybeFree ms1) ~f2
      | null ms1  = f1
    pickFree f1@(MaybeFree ms1) f2@(MaybeFree ms2)
      | null ms2  = f2
      | otherwise = f1
    pickFree f1@(MaybeFree ms1) NotFree = f1
    pickFree NotFree f2 = f2

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

instance (Reduce a, ForceNotFree a) => ForceNotFree (Arg a) where
  -- Precomputed free variables are stored in the Arg so reduceIf outside the
  -- traverse.
  forceNotFree' = reduceIfFreeVars (traverse forceNotFree')

instance (Reduce a, ForceNotFree a, TermSubst a) => ForceNotFree (Dom a) where
  forceNotFree' = traverse forceNotFreeR

instance (Reduce a, ForceNotFree a) => ForceNotFree (Abs a) where
  -- Reduction stops at abstractions (lambda/pi) so do reduceIf/forceNotFreeR here.
  forceNotFree' = \case
    a@NoAbs{} -> traverse forceNotFreeR a
    a@Abs{}   -> reduceIfFreeVars (local (\(FREnv x nfs ms e) -> FREnv (x + 1) nfs ms e) . traverse forceNotFree') a

instance ForceNotFree a => ForceNotFree [a] where
  forceNotFree' = \case
    []     -> pure []
    (a:as) -> (:) <$> forceNotFree' a <*> forceNotFree' as

instance (Reduce a, ForceNotFree a) => ForceNotFree (Elim' a) where
  -- There's an Arg inside Elim' which stores precomputed free vars, so let's
  -- not skip over that.
  forceNotFree' = \case
    Apply arg    -> Apply <$> forceNotFree' arg
    e@Proj{}     -> pure e
    IApply x y r -> IApply <$> forceNotFreeR x <*> forceNotFreeR y <*> forceNotFreeR r

instance ForceNotFree Type where
  forceNotFree' (El s t) = El <$> forceNotFree' s <*> forceNotFree' t

instance ForceNotFree Term where
  forceNotFree' t = do
    FREnv locals wantToNotFree metas _ <- ask
    case t of
      Var x es -> do
        FRState xs mxs <- get
        let x' = x - locals
        if (x >= locals && VarSet.member x' wantToNotFree) then do
          put $! FRState (VarSet.delete x' xs) (IntMap.insert x' metas mxs)
          Var x <$> forceNotFree' es
        else
          Var x <$> forceNotFree' es
      Def f es   -> Def f    <$> forceNotFree' es
      Con c h es -> Con c h  <$> forceNotFree' es
      MetaV m es -> local (\(FREnv x nfs ms e) -> FREnv x nfs (insertMetaSet m ms) e) $ MetaV m <$> forceNotFree' es
      Lam h b    -> Lam h    <$> forceNotFree' b
      Pi a b     -> Pi       <$> forceNotFree' a <*> forceNotFree' b  -- Dom and Abs do reduceIf so not needed here
      Sort s     -> Sort     <$> forceNotFree' s
      Level l    -> Level    <$> forceNotFree' l
      DontCare t -> DontCare <$> forceNotFreeR t  -- Reduction stops at DontCare so reduceIf
      t@Lit{}    -> pure t
      t@Dummy{}  -> pure t

instance ForceNotFree Level where
  forceNotFree' (Max m as) = Max m <$> forceNotFree' as

instance ForceNotFree PlusLevel where
  forceNotFree' (Plus k a) = Plus k <$> forceNotFree' a

instance ForceNotFree Sort where
  -- Reduce for sorts already goes under all sort constructors, so we can get
  -- away without forceNotFreeR here.
  forceNotFree' = \case
    Univ u l       -> Univ u <$> forceNotFree' l
    PiSort a b c   -> PiSort <$> forceNotFree' a <*> forceNotFree' b <*> forceNotFree' c
    FunSort a b    -> FunSort <$> forceNotFree' a <*> forceNotFree' b
    UnivSort s     -> UnivSort <$> forceNotFree' s
    MetaS x es     -> MetaS x <$> forceNotFree' es
    DefS d es      -> DefS d <$> forceNotFree' es
    s@(Inf _ _)    -> pure s
    s@SizeUniv     -> pure s
    s@LockUniv     -> pure s
    s@LevelUniv    -> pure s
    s@IntervalUniv -> pure s
    s@DummyS{}     -> pure s
