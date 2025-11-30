{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -ddump-simpl -dsuppress-all -dno-suppress-type-signatures -ddump-to-file #-}
{-# OPTIONS_GHC -fworker-wrapper-cbv #-}

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

module Agda.TypeChecking.Free.LazyNew where

import Control.Applicative hiding (empty)
import Control.Monad.Reader ( MonadReader(..), asks)
import Agda.Utils.StrictReader

import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as VarSet

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Semigroup ( Any(..), All(..) )

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List1 (List1)
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Semigroup
import Agda.Utils.Singleton
import Agda.Utils.Size

--------------------------------------------------------------------------------

newtype MetaSet = MetaSet { theMetaSet :: HashSet MetaId }
  deriving (Eq, Show, Null, Semigroup, Monoid)

insertMetaSet :: MetaId -> MetaSet -> MetaSet
insertMetaSet m (MetaSet ms) = MetaSet $ HashSet.insert m ms

foldrMetaSet :: (MetaId -> a -> a) -> a -> MetaSet -> a
foldrMetaSet f e ms = HashSet.foldr f e $ theMetaSet ms

metaSetToBlocker :: MetaSet -> Blocker
metaSetToBlocker ms = unblockOnAny $ foldrMetaSet (Set.insert . unblockOnMeta) Set.empty ms

data FlexRig' a
  = Flexible !a   -- ^ In arguments of metas.
                  --   The set of metas is used by ''Agda.TypeChecking.Rewriting.NonLinMatch''
                  --   to generate the right blocking information.
                  --   The semantics is that the status of a variable occurrence may change
                  --   if one of the metas in the set gets solved.  We may say the occurrence
                  --   is tainted by the meta variables in the set.
  | WeaklyRigid   -- ^ In arguments to variables and definitions.
  | Unguarded     -- ^ In top position, or only under inductive record constructors (unit).
  | StronglyRigid -- ^ Under at least one and only inductive constructors.
  deriving (Eq, Show, Functor, Foldable)

type FlexRig = FlexRig' MetaSet

-- | Where should we skip sorts in free variable analysis?
data IgnoreSorts
  = IgnoreNot            -- ^ Do not skip.
  | IgnoreInAnnotations  -- ^ Skip when annotation to a type.
  | IgnoreAll            -- ^ Skip unconditionally.
  deriving (Eq, Show)

class (Monoid (Collect r), Singleton MetaId (FlexRigItem r), Monoid (FlexRigItem r)) => ComputeFree r where
  type Collect r
  type FlexRigItem r
  underBinders'     :: Int -> r -> r
  underConstructor' :: ConHead -> Elims -> r -> r
  underModality'    :: Modality -> r -> r
  underRelevance'   :: Relevance -> r -> r
  underFlexRig'     :: FlexRig' (FlexRigItem r) -> r -> r
  underQuantity'    :: Quantity -> r -> r
  variable'         :: Int -> r -> Collect r
  ignoreSorts'      :: IgnoreSorts
  underBinders'     _ r = r
  underConstructor' _ _ r = r
  underModality'    _ r = r
  underRelevance'   _ r = r
  underFlexRig'     _ r = r
  underQuantity'    _ r = r

ignoreSorts :: forall r m. MonadReader r m => ComputeFree r => m IgnoreSorts
ignoreSorts = pure (ignoreSorts' @r)

underBinders :: MonadReader r m => ComputeFree r => Int -> m a -> m a
underBinders = local . underBinders'

underBinder :: MonadReader r m => ComputeFree r => m a -> m a
underBinder = underBinders 1

underConstructor :: MonadReader r m => ComputeFree r => ConHead -> Elims -> m a -> m a
underConstructor hd es = local (underConstructor' hd es)

underModality :: MonadReader r m => ComputeFree r => Modality -> m a -> m a
underModality = local . underModality'

underRelevance :: MonadReader r m => ComputeFree r => Relevance -> m a -> m a
underRelevance = local . underRelevance'

underFlexRig :: MonadReader r m => ComputeFree r => FlexRig' (FlexRigItem r) -> m a -> m a
underFlexRig = local . underFlexRig'

underQuantity :: MonadReader r m => ComputeFree r => Quantity -> m a -> m a
underQuantity = local . underQuantity'

variable :: MonadReader r m => ComputeFree r => Int -> m (Collect r)
variable x = variable' x <$!> ask

--------------------------------------------------------------------------------

class Free t where
  freeVars :: ComputeFree r => t -> Reader r (Collect r)

  default freeVars :: (t ~ f b, Foldable f, Free b, ComputeFree r) => t -> Reader r (Collect r)
  freeVars = foldr (\b c -> freeVars b <> c) mempty

instance Free Term where
  freeVars t = case t of
    Var n ts ->
      -- #4484: avoid projected variables being treated as StronglyRigid
      if any (\case Proj{} -> True; _ -> False) ts then
        underFlexRig WeaklyRigid $ variable n <> freeVars ts
      else
        variable n <> underFlexRig WeaklyRigid (freeVars ts)

    -- λ is not considered guarding, as
    -- we cannot prove that x ≡ λy.x is impossible.
    Lam _ t      -> underFlexRig WeaklyRigid $ freeVars t
    Lit _        -> mempty
    Def _ ts     -> underFlexRig WeaklyRigid $ freeVars ts
      -- because we are not in TCM
      -- we cannot query whether we are dealing with a data/record (strongly r.)
      -- or a definition by pattern matching (weakly rigid)
      -- thus, we approximate, losing that x = List x is unsolvable
    Con c _ ts   -> underConstructor c ts $ freeVars ts
    -- Pi is not guarding, since we cannot prove that A ≡ B → A is impossible.
    -- Even as we do not permit infinite type expressions,
    -- we cannot prove their absence (as Set is not inductive).
    -- Also, this is incompatible with univalence (HoTT).
    Pi a b       -> freeVars (a, b)
    Sort s       -> freeVars s
    Level l      -> freeVars l
    MetaV m ts   -> underFlexRig (Flexible $ singleton m) $ freeVars ts
    DontCare mt  -> underModality (Modality irrelevant unitQuantity unitCohesion unitPolarity) $ freeVars mt
    Dummy{}      -> mempty

instance Free t => Free (Elim' t) where
  freeVars (Apply t)      = freeVars t
  freeVars (Proj{})       = mempty
  freeVars (IApply x y r) = freeVars (x,y,r)

instance Free t => Free (Type' t) where
  freeVars (El s t) =
    ifM ((IgnoreNot ==) <$> ignoreSorts)
      {- then -} (freeVars (s, t))
      {- else -} (freeVars t)

instance Free Sort where
  freeVars s =
    ifM ((IgnoreAll ==) <$> ignoreSorts) mempty $ {- else -}
    case s of
      Univ _ a       -> freeVars a
      Inf _ _        -> mempty
      SizeUniv       -> mempty
      LockUniv       -> mempty
      LevelUniv      -> mempty
      IntervalUniv   -> mempty
      PiSort a s1 s2 -> underFlexRig (Flexible mempty) (freeVars $ unDom a) <>
                        underFlexRig WeaklyRigid (freeVars (s1, s2))
      FunSort s1 s2  -> freeVars s1 <> freeVars s2
      UnivSort s     -> underFlexRig WeaklyRigid $ freeVars s
      MetaS x es     -> underFlexRig (Flexible $ singleton x) $ freeVars es
      DefS _ es      -> underFlexRig WeaklyRigid $ freeVars es
      DummyS{}       -> mempty

instance Free t => Free [t]
instance Free t => Free (List1 t)
instance Free t => Free (Maybe t)
instance Free t => Free (WithHiding t)
instance Free t => Free (Named nm t)
instance Free t => Free (Ranged t)

instance (Free a, Free b) => Free (a, b) where
  {-# INLINE freeVars #-}
  freeVars (a, b) = freeVars a <> freeVars b

instance (Free a, Free b, Free c) => Free (a, b, c) where
  {-# INLINE freeVars #-}
  freeVars (a, b, c) = freeVars a <> freeVars b <> freeVars c

instance Free Level where
  freeVars (Max _ as) = freeVars as

instance Free t => Free (PlusLevel' t) where
  freeVars (Plus _ l) = freeVars l

instance Free t => Free (Arg t) where
  freeVars t = underModality (getModality t) $ freeVars $ unArg t

instance Free t => Free (Dom t) where
  freeVars d = freeVars (domTactic d, unDom d)

instance Free t => Free (Abs t) where
  freeVars (Abs   _ b) = underBinder $ freeVars b
  freeVars (NoAbs _ b) = freeVars b

instance Free t => Free (Tele t) where
  freeVars EmptyTel          = mempty
  freeVars (ExtendTel t tel) = freeVars (t, tel)

instance Free Clause where
  freeVars cl = underBinders (size $ clauseTel cl) $ freeVars $ clauseBody cl

instance Free EqualityView where
  freeVars = \case
    OtherType t                   -> freeVars t
    IdiomType t                   -> freeVars t
    EqualityType _r s _eq l t a b -> freeVars (s, l, (t, a, b))

--------------------------------------------------------------------------------

-- | 'FlexRig' aggregation (additive operation of the semiring).
--   For combining occurrences of the same variable in subterms.
--   This is a refinement of the 'max' operation for 'FlexRig'
--   which would work if 'Flexible' did not have the 'MetaSet' as an argument.
--   Now, to aggregate two 'Flexible' occurrences, we union the involved 'MetaSet's.
addFlexRig :: Semigroup a => FlexRig' a -> FlexRig' a -> FlexRig' a
addFlexRig = curry $ \case
  -- StronglyRigid is dominant
  (StronglyRigid, _) -> StronglyRigid
  (_, StronglyRigid) -> StronglyRigid
  -- Next is Unguarded
  (Unguarded, _) -> Unguarded
  (_, Unguarded) -> Unguarded
  -- Then WeaklyRigid
  (WeaklyRigid, _) -> WeaklyRigid
  (_, WeaklyRigid) -> WeaklyRigid
  -- Least is Flexible.  We union the meta sets, as the variable
  -- is tainted by all of the involved meta variable.
  (Flexible ms1, Flexible ms2) -> Flexible $ ms1 <> ms2
{-# SPECIALIZE NOINLINE addFlexRig :: FlexRig' MetaSet -> FlexRig' MetaSet -> FlexRig' MetaSet #-}
{-# SPECIALIZE NOINLINE addFlexRig :: FlexRig' () -> FlexRig' () -> FlexRig' () #-}

-- | Unit for 'addFlexRig'.
zeroFlexRig :: Monoid a => FlexRig' a
zeroFlexRig = Flexible mempty

-- | Absorptive for 'addFlexRig'.
omegaFlexRig :: FlexRig' a
omegaFlexRig = StronglyRigid

-- | 'FlexRig' composition (multiplicative operation of the semiring).
--   For accumulating the context of a variable.
--
--   'Flexible' is dominant.  Once we are under a meta, we are flexible
--   regardless what else comes.  We taint all variable occurrences
--   under a meta by this meta.
--
--   'WeaklyRigid' is next in strength.  Destroys strong rigidity.
--
--   'StronglyRigid' is still dominant over 'Unguarded'.
--
--   'Unguarded' is the unit.  It is the top (identity) context.
--
composeFlexRig :: Semigroup a => FlexRig' a -> FlexRig' a -> FlexRig' a
composeFlexRig x y = case (x, y) of
    (Flexible ms1 , Flexible ms2 ) -> Flexible $ ms1 <> ms2
    (Flexible ms1 , _            ) -> Flexible ms1
    (_            , Flexible ms2 ) -> Flexible ms2
    (WeaklyRigid  , _            ) -> WeaklyRigid
    (_            , WeaklyRigid  ) -> WeaklyRigid
    (StronglyRigid, _            ) -> StronglyRigid
    (_            , StronglyRigid) -> StronglyRigid
    (Unguarded    , Unguarded    ) -> Unguarded
{-# SPECIALIZE NOINLINE composeFlexRig :: FlexRig' MetaSet -> FlexRig' MetaSet -> FlexRig' MetaSet #-}
{-# SPECIALIZE NOINLINE composeFlexRig :: FlexRig' () -> FlexRig' () -> FlexRig' () #-}

-- | Unit for 'composeFlexRig'.
oneFlexRig :: FlexRig' a
oneFlexRig = Unguarded


---------------------------------------------------------------------------
-- * Multi-dimensional feature vector for variable occurrence (semigroup)

-- | Occurrence of free variables is classified by several dimensions.
--   Currently, we have 'FlexRig' and 'Modality'.
data VarOcc' a = VarOcc
  { varFlexRig   :: !(FlexRig' a)
  , varModality  :: !Modality
  }
  deriving (Show)
type VarOcc = VarOcc' MetaSet

-- | Equality up to origin.
instance Eq a => Eq (VarOcc' a) where
  VarOcc fr m == VarOcc fr' m' = fr == fr' && sameModality m m'

-- | The default way of aggregating free variable info from subterms is by adding
--   the variable occurrences.  For instance, if we have a pair @(t₁,t₂)@ then
--   and @t₁@ has @o₁@ the occurrences of a variable @x@
--   and @t₂@ has @o₂@ the occurrences of the same variable, then
--   @(t₁,t₂)@ has @mappend o₁ o₂@ occurrences of that variable.
--
--   From counting 'Quantity', we extrapolate this to 'FlexRig' and 'Relevance':
--   we care most about about 'StronglyRigid' 'Relevant' occurrences.
--   E.g., if @t₁@ has a 'StronglyRigid' occurrence and @t₂@ a 'Flexible' occurrence,
--   then @(t₁,t₂)@ still has a 'StronglyRigid' occurrence.
--   Analogously, @Relevant@ occurrences count most, as we wish e.g. to forbid
--   relevant occurrences of variables that are declared to be irrelevant.
--
--   'VarOcc' forms a semiring, and this monoid is the addition of the semiring.
instance Semigroup a => Semigroup (VarOcc' a) where
  VarOcc o m <> VarOcc o' m' = VarOcc (addFlexRig o o') (addModality m m')

-- | The neutral element for variable occurrence aggregation is least serious
--   occurrence: flexible, irrelevant.
--   This is also the absorptive element for 'composeVarOcc', if we ignore
--   the 'MetaSet' in 'Flexible'.
instance (Semigroup a, Monoid a) => Monoid (VarOcc' a) where
  mempty  = VarOcc (Flexible mempty) zeroModality

-- | The absorptive element of variable occurrence under aggregation:
--   strongly rigid, relevant.
topVarOcc :: VarOcc' a
topVarOcc = VarOcc StronglyRigid topModality

-- | First argument is the outer occurrence (context) and second is the inner.
--   This multiplicative operation is to modify an occurrence under a context.
composeVarOcc :: Semigroup a => VarOcc' a -> VarOcc' a -> VarOcc' a
composeVarOcc (VarOcc o m) (VarOcc o' m') = VarOcc (composeFlexRig o o') (composeModality m m')
  -- We use the multipicative modality monoid (composition).

oneVarOcc :: VarOcc' a
oneVarOcc = VarOcc Unguarded unitModality
