
-- | Computing the free variables of a term lazily.
--
-- We implement a reduce (traversal into monoid) over internal syntax
-- for a generic collection (monoid with singletons).  This should allow
-- a more efficient test for the presence of a particular variable.
--
-- Worst-case complexity does not change (i.e. the case when a variable
-- does not occur), but best case-complexity does matter.  For instance,
-- see 'Agda.TypeChecking.Substitute.mkAbs': each time we construct
-- a dependent function type, we check whether it is actually dependent.
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
-- For further reading on semirings and semimodules for variable occurrence,
-- see e.g. Conor McBrides "I got plenty of nuttin'" (Wadlerfest 2016).
-- There, he treats the "quantity" dimension of variable occurrences.
--
-- The semiring has an additive operation for combining occurrences of subterms,
-- and a multiplicative operation of representing function composition.  E.g.
-- if variable @x@ appears @o@ in term @u@, but @u@ appears in context @q@ in
-- term @t@ then occurrence of variable @x@ coming from @u@ is accounted for
-- as @q o@ in @t@.
--
-- Consider example @(λ{ x → (x,x)}) y@:
--
--   * Variable @x@ occurs once unguarded in @x@.
--
--   * It occurs twice unguarded in the aggregation @x@ @x@
--
--   * Inductive constructor @,@ turns this into two strictly rigid occurrences.
--
--     If @,@ is a record constructor, then we stay unguarded.
--
--   * The function @({λ x → (x,x)})@ provides a context for variable @y@.
--     This context can be described as weakly rigid with quantity two.
--
--   * The final occurrence of @y@ is obtained as composing the context with
--     the occurrence of @y@ in itself (which is the unit for composition).
--     Thus, @y@ occurs weakly rigid with quantity two.
--
-- It is not a given that the context can be described in the same way
-- as the variable occurrence.  However, for quantity it is the case
-- and we obtain a semiring of occurrences with 0, 1, and even ω, which
-- is an absorptive element for addition.

module Agda.TypeChecking.Free.Lazy (
    module Agda.TypeChecking.Free.Base
  , module Agda.TypeChecking.Free.Lazy
  ) where

import Control.Applicative hiding (empty)
import Control.Monad.Reader ( MonadReader(..), asks, ReaderT, Reader, runReader )

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Set (Set)
import qualified Data.Set as Set

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Free.Base

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List1 (List1)
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Semigroup
import Agda.Utils.Singleton
import Agda.Utils.Size

--------------------------------------------------------------------------------

type FreeT a b m c = ReaderT (FreeEnv' a b c) m c
type FreeM a c = Reader (FreeEnv' a IgnoreSorts c) c

-- | Run function for FreeM.
runFreeM :: IsVarSet a c => SingleVar c -> IgnoreSorts -> FreeM a c -> c
runFreeM single i m = runReader m $ initFreeEnv i single

instance (Monad m, Monoid c) => Monoid (FreeT a b m c) where
  mempty  = pure mempty
  mappend = (<>)
  mconcat = mconcat <.> sequence

-- | Base case: a variable.
variable :: (Monad m, IsVarSet a c) => Int -> FreeT a b m c
variable n = do
  o <- asks feFlexRig
  r <- asks feModality
  s <- asks feSingleton
  return $ withVarOcc (VarOcc o r) (s $ Just n)

-- | Subtract, but return Nothing if result is negative.
subVar :: Int -> Maybe Variable -> Maybe Variable
-- subVar n x = x >>= \ i -> (i - n) <$ guard (n <= i)
subVar n x = do
  i <- x
  guard $ i >= n
  return $ i - n

-- | Going under a binder.
underBinder :: MonadReader (FreeEnv' a b c) m => m z -> m z
underBinder = underBinder' 1

-- | Going under @n@ binders.
underBinder' :: MonadReader (FreeEnv' a b c) m => Nat -> m z -> m z
underBinder' n = local $ \ e -> e { feSingleton = feSingleton e . subVar n }

-- | Changing the 'Modality'.
underModality :: (MonadReader r m, LensModality r, LensModality o) => o -> m z -> m z
underModality = local . mapModality . composeModality . getModality

-- | Changing the 'Relevance'.
underRelevance :: (MonadReader r m, LensRelevance r, LensRelevance o) => o -> m z -> m z
underRelevance = local . mapRelevance . composeRelevance . getRelevance

-- | In the given computation the 'Quantity' is locally scaled using
-- the 'Quantity' of the first argument.
underQuantity ::
  (MonadReader r m, LensQuantity r, LensQuantity o) => o -> m a -> m a
underQuantity = local . mapQuantity . composeQuantity . getQuantity

-- | Changing the 'FlexRig' context.
underFlexRig :: (MonadReader r m, LensFlexRig r a, Semigroup a, LensFlexRig o a) => o -> m z -> m z
underFlexRig = local . over lensFlexRig . composeFlexRig . view lensFlexRig

-- | What happens to the variables occurring under a constructor?
underConstructor :: (MonadReader r m, LensFlexRig r a, Semigroup a) => ConHead -> Elims -> m z -> m z
underConstructor (ConHead _c _d i fs) es =
  case i of
    -- Coinductive (record) constructors admit infinite cycles:
    CoInductive -> underFlexRig WeaklyRigid
    -- Inductive constructors do not admit infinite cycles:
    Inductive   | natSize es == natSize fs -> underFlexRig StronglyRigid
                | otherwise                -> underFlexRig WeaklyRigid
    -- Jesper, 2020-10-22: Issue #4995: treat occurrences in non-fully
    -- applied constructors as weakly rigid.
    -- Ulf, 2019-10-18: Now the termination checker treats inductive recursive records
    -- the same as datatypes, so absense of infinite cycles can be proven in Agda, and thus
    -- the unifier is allowed to do it too. Test case: test/Succeed/Issue1271a.agda
    -- WAS:
    -- -- Inductive record constructors do not admit infinite cycles,
    -- -- but this cannot be proven inside Agda.
    -- -- Thus, unification should not prove it either.

---------------------------------------------------------------------------
-- * Recursively collecting free variables.

-- | Gather free variables in a collection.
class Free t where
  -- Misplaced SPECIALIZE pragma:
  -- {-# SPECIALIZE freeVars' :: a -> FreeM Any #-}
  -- So you cannot specialize all instances in one go. :(
  freeVars' :: IsVarSet a c => t -> FreeM a c

  default freeVars' :: (t ~ f b, Foldable f, Free b) => IsVarSet a c => t -> FreeM a c
  freeVars' = foldMap freeVars'


instance Free Term where
  -- SPECIALIZE instance does not work as well, see
  -- https://ghc.haskell.org/trac/ghc/ticket/10434#ticket
  -- {-# SPECIALIZE instance Free Term All #-}
  -- {-# SPECIALIZE freeVars' :: Term -> FreeM Any #-}
  -- {-# SPECIALIZE freeVars' :: Term -> FreeM All #-}
  -- {-# SPECIALIZE freeVars' :: Term -> FreeM VarSet #-}
  freeVars' t = case unSpine t of -- #4484: unSpine to avoid projected variables being treated as StronglyRigid
    Var n ts     -> variable n `mappend` do underFlexRig WeaklyRigid $ freeVars' ts
    -- λ is not considered guarding, as
    -- we cannot prove that x ≡ λy.x is impossible.
    Lam _ t      -> underFlexRig WeaklyRigid $ freeVars' t
    Lit _        -> mempty
    Def _ ts     -> underFlexRig WeaklyRigid $ freeVars' ts  -- because we are not in TCM
      -- we cannot query whether we are dealing with a data/record (strongly r.)
      -- or a definition by pattern matching (weakly rigid)
      -- thus, we approximate, losing that x = List x is unsolvable
    Con c _ ts   -> underConstructor c ts $ freeVars' ts
    -- Pi is not guarding, since we cannot prove that A ≡ B → A is impossible.
    -- Even as we do not permit infinite type expressions,
    -- we cannot prove their absence (as Set is not inductive).
    -- Also, this is incompatible with univalence (HoTT).
    Pi a b       -> freeVars' (a,b)
    Sort s       -> underRelevance shapeIrrelevant $ freeVars' s
    Level l      -> freeVars' l
    MetaV m ts   -> underFlexRig (Flexible $ singleton m) $ freeVars' ts
    DontCare mt  -> underModality (Modality irrelevant unitQuantity unitCohesion unitPolarity) $ freeVars' mt
    Dummy{}      -> mempty

instance Free t => Free (Type' t) where
  freeVars' (El s t) =
    ifM (asks ((IgnoreNot ==) . feIgnoreSorts))
      {- then -} (freeVars' (s, t))
      {- else -} (freeVars' t)

instance Free Sort where
  freeVars' s =
    ifM (asks ((IgnoreAll ==) . feIgnoreSorts)) mempty $ {- else -}
    case s of
      Univ _ a   -> freeVars' a
      Inf _ _    -> mempty
      SizeUniv   -> mempty
      LockUniv   -> mempty
      LevelUniv  -> mempty
      IntervalUniv -> mempty
      PiSort a s1 s2 -> underFlexRig (Flexible mempty) (freeVars' $ unDom a) `mappend`
                        underFlexRig WeaklyRigid (freeVars' (s1, s2))
      FunSort s1 s2 -> freeVars' s1 `mappend` freeVars' s2
      UnivSort s -> underFlexRig WeaklyRigid $ freeVars' s
      MetaS x es -> underFlexRig (Flexible $ singleton x) $ freeVars' es
      DefS _ es  -> underFlexRig WeaklyRigid $ freeVars' es
      DummyS{}   -> mempty

instance Free Level where
  freeVars' (Max _ as) = freeVars' as

instance Free t => Free (PlusLevel' t) where
  freeVars' (Plus _ l)    = freeVars' l

instance Free t => Free [t]
instance Free t => Free (List1 t)
instance Free t => Free (Maybe t)
instance Free t => Free (WithHiding t)
instance Free t => Free (Named nm t)
instance Free t => Free (Ranged t)

instance (Free t, Free u) => Free (t, u) where
  freeVars' (t, u) = freeVars' t `mappend` freeVars' u

instance (Free t, Free u, Free v) => Free (t, u, v) where
  freeVars' (t, u, v) = freeVars' t `mappend` freeVars' u `mappend` freeVars' v

instance Free t => Free (Elim' t) where
  freeVars' (Apply t) = freeVars' t
  freeVars' (Proj{} ) = mempty
  freeVars' (IApply x y r) = freeVars' (x,y,r)

instance Free t => Free (Arg t) where
  freeVars' t = underModality (getModality t) $ freeVars' $ unArg t

instance Free t => Free (Dom t) where
  freeVars' d = freeVars' (domTactic d, unDom d)

instance Free t => Free (Abs t) where
  freeVars' (Abs   _ b) = underBinder $ freeVars' b
  freeVars' (NoAbs _ b) = freeVars' b

instance Free t => Free (Tele t) where
  freeVars' EmptyTel          = mempty
  freeVars' (ExtendTel t tel) = freeVars' (t, tel)

instance Free Clause where
  freeVars' cl = underBinder' (size $ clauseTel cl) $ freeVars' $ clauseBody cl

instance Free EqualityView where
  freeVars' = \case
    OtherType t -> freeVars' t
    IdiomType t -> freeVars' t
    EqualityType _r s _eq l t a b -> freeVars' (s, l, [t, a, b])
