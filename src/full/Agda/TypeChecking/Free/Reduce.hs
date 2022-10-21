
-- | Free variable check that reduces the subject to make certain variables not
--   free. Used when pruning metavariables in Agda.TypeChecking.MetaVars.Occurs.
module Agda.TypeChecking.Free.Reduce
  ( ForceNotFree
  , forceNotFree
  , reallyFree
  , IsFree(..)
  ) where

import Prelude hiding (null)

import Control.Monad.Reader
import Control.Monad.State

import qualified Data.IntMap as IntMap
import Data.IntMap (IntMap)
import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Free
import Agda.TypeChecking.Free.Precompute

import Agda.Utils.Monad
import Agda.Utils.Null

-- | A variable can either not occur (`NotFree`) or it does occur
--   (`MaybeFree`).  In the latter case, the occurrence may disappear
--   depending on the instantiation of some set of metas.
data IsFree
  = MaybeFree MetaSet
  | NotFree
  deriving (Eq, Show)

-- | Try to enforce a set of variables not occurring in a given
--   type. Returns a possibly reduced version of the type and for each
--   of the given variables whether it is either not free, or
--   maybe free depending on some metavariables.
forceNotFree :: (ForceNotFree a, Reduce a, MonadReduce m)
             => IntSet -> a -> m (IntMap IsFree, a)
forceNotFree xs a = do
  -- Initially, all variables are marked as `NotFree`. This is changed
  -- to `MaybeFree` when we find an occurrence.
  let mxs = IntMap.fromSet (const NotFree) xs
  (a, mxs) <- runStateT (runReaderT (forceNotFreeR $ precomputeFreeVars_ a) mempty) mxs
  return (mxs, a)

-- | Checks if the given term contains any free variables that are in
--   the given set of variables, possibly reducing the term in the
--   process.  Returns `Right Nothing` if there are such variables,
--   `Right (Just v')` if there are none (where v' is the possibly
--   reduced version of the given term) or `Left b` if the problem is
--   blocked on a meta.
reallyFree :: (MonadReduce m, Reduce a, ForceNotFree a)
           => IntSet -> a -> m (Either Blocked_ (Maybe a))
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
    pickFree f1@(MaybeFree ms1) f2
      | null ms1  = f1
    pickFree f1@(MaybeFree ms1) f2@(MaybeFree ms2)
      | null ms2  = f2
      | otherwise = f1
    pickFree f1@(MaybeFree ms1) NotFree = f1
    pickFree NotFree f2 = f2

type MonadFreeRed m =
  ( MonadReader MetaSet m
  , MonadState (IntMap IsFree) m
  , MonadReduce m
  )

class (PrecomputeFreeVars a, Subst a) => ForceNotFree a where
  -- Reduce the argument if necessary, to make as many as possible of
  -- the variables in the state not free. Updates the state, marking
  -- the variables that couldn't be make not free as `MaybeFree`. By
  -- updating the state as soon as a variable can not be reduced away,
  -- we avoid trying to get rid of it in other places.
  forceNotFree' :: (MonadFreeRed m) => a -> m a

-- Return the set of variables for which there is still hope that they
-- may not occur.
varsToForceNotFree :: (MonadFreeRed m) => m IntSet
varsToForceNotFree = gets (IntMap.keysSet . (IntMap.filter (== NotFree)))

-- Reduce the argument if there are offending free variables. Doesn't call the
-- continuation when no reduction is required.
reduceIfFreeVars :: (Reduce a, ForceNotFree a, MonadFreeRed m)
                 => (a -> m a) -> a -> m a
reduceIfFreeVars k a = do
  xs <- varsToForceNotFree
  let fvs     = precomputedFreeVars a
      notfree = IntSet.disjoint xs fvs
  if notfree
    then return a
    else k . precomputeFreeVars_ =<< reduce a

-- Careful not to define forceNotFree' = forceNotFreeR since that would loop.
forceNotFreeR :: (Reduce a, ForceNotFree a, MonadFreeRed m)
              => a -> m a
forceNotFreeR = reduceIfFreeVars forceNotFree'

instance (Reduce a, ForceNotFree a) => ForceNotFree (Arg a) where
  -- Precomputed free variables are stored in the Arg so reduceIf outside the
  -- traverse.
  forceNotFree' = reduceIfFreeVars (traverse forceNotFree')

instance (Reduce a, ForceNotFree a, TermSubst a) => ForceNotFree (Dom a) where
  forceNotFree' = traverse forceNotFreeR

instance (Reduce a, ForceNotFree a) => ForceNotFree (Abs a) where
  -- Reduction stops at abstractions (lambda/pi) so do reduceIf/forceNotFreeR here.
  forceNotFree' a@NoAbs{} = traverse forceNotFreeR a
  forceNotFree' a@Abs{} =
    -- Shift variables up when going under the abstraction and back down when
    -- coming out of it. Since we never add new indices to the state
    -- there's no danger of getting negative indices.
    reduceIfFreeVars (bracket_ (modify $ IntMap.mapKeys succ) (\ _ -> modify $ IntMap.mapKeys pred) .
                      traverse forceNotFree') a

instance ForceNotFree a => ForceNotFree [a] where
  forceNotFree' = traverse forceNotFree'

instance (Reduce a, ForceNotFree a) => ForceNotFree (Elim' a) where
  -- There's an Arg inside Elim' which stores precomputed free vars, so let's
  -- not skip over that.
  forceNotFree' (Apply arg)    = Apply <$> forceNotFree' arg
  forceNotFree' e@Proj{}       = return e
  forceNotFree' (IApply x y r) = IApply <$> forceNotFreeR x <*> forceNotFreeR y <*> forceNotFreeR r

instance ForceNotFree Type where
  forceNotFree' (El s t) = El <$> forceNotFree' s <*> forceNotFree' t

instance ForceNotFree Term where
  forceNotFree' = \case
    Var x es   -> do
      metas <- ask
      modify $ IntMap.adjust (const $ MaybeFree metas) x
      Var x <$> forceNotFree' es
    Def f es   -> Def f    <$> forceNotFree' es
    Con c h es -> Con c h  <$> forceNotFree' es
    MetaV x es -> local (insertMetaSet x) $
                  MetaV x  <$> forceNotFree' es
    Lam h b    -> Lam h    <$> forceNotFree' b
    Pi a b     -> Pi       <$> forceNotFree' a <*> forceNotFree' b  -- Dom and Abs do reduceIf so not needed here
    Sort s     -> Sort     <$> forceNotFree' s
    Level l    -> Level    <$> forceNotFree' l
    DontCare t -> DontCare <$> forceNotFreeR t  -- Reduction stops at DontCare so reduceIf
    t@Lit{}    -> return t
    t@Dummy{}  -> return t

instance ForceNotFree Level where
  forceNotFree' (Max m as) = Max m <$> forceNotFree' as

instance ForceNotFree PlusLevel where
  forceNotFree' (Plus k a) = Plus k <$> forceNotFree' a

instance ForceNotFree Sort where
  -- Reduce for sorts already goes under all sort constructors, so we can get
  -- away without forceNotFreeR here.
  forceNotFree' = \case
    Type l     -> Type     <$> forceNotFree' l
    Prop l     -> Prop     <$> forceNotFree' l
    SSet l     -> SSet     <$> forceNotFree' l
    PiSort a b c -> PiSort <$> forceNotFree' a <*> forceNotFree' b <*> forceNotFree' c
    FunSort a b -> FunSort <$> forceNotFree' a <*> forceNotFree' b
    UnivSort s -> UnivSort <$> forceNotFree' s
    MetaS x es -> MetaS x  <$> forceNotFree' es
    DefS d es  -> DefS d   <$> forceNotFree' es
    s@(Inf _ _)-> return s
    s@SizeUniv -> return s
    s@LockUniv -> return s
    s@IntervalUniv -> return s
    s@DummyS{} -> return s
