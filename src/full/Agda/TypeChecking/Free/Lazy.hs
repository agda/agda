{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeFamilies               #-}

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

module Agda.TypeChecking.Free.Lazy where

import Control.Applicative hiding (empty)
import Control.Monad.Reader


import Data.Foldable (Foldable, foldMap)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Monoid ( Monoid, mempty, mappend, mconcat )
import Data.Semigroup ( Semigroup, (<>) )



import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Singleton
import Agda.Utils.Size

---------------------------------------------------------------------------
-- * Set of meta variables.

-- | A set of meta variables.  Forms a monoid under union.

newtype MetaSet = MetaSet { theMetaSet :: IntSet }
  deriving (Eq, Show, Null, Semigroup, Monoid)

instance Singleton MetaId MetaSet where
  singleton = MetaSet . singleton . metaId

insertMetaSet :: MetaId -> MetaSet -> MetaSet
insertMetaSet (MetaId m) (MetaSet ms) = MetaSet $ IntSet.insert m ms

foldrMetaSet :: (MetaId -> a -> a) -> a -> MetaSet -> a
foldrMetaSet f e ms = IntSet.foldr (f . MetaId) e $ theMetaSet ms

---------------------------------------------------------------------------
-- * Flexible and rigid occurrences (semigroup)

-- | Depending on the surrounding context of a variable,
--   it's occurrence can be classified as flexible or rigid,
--   with finer distinctions.
--
--   The constructors are listed in increasing order (wrt. information content).
data FlexRig' a
  = Flexible a        -- ^ In arguments of metas.
                      --   The set of metas is used by ''Agda.TypeChecking.Rewriting.NonLinMatch''
                      --   to generate the right blocking information.
                      --   The semantics is that the status of a variable occurrence may change
                      --   if one of the metas in the set gets solved.  We may say the occurrence
                      --   is tainted by the meta variables in the set.
  | WeaklyRigid       -- ^ In arguments to variables and definitions.
  | Unguarded         -- ^ In top position, or only under inductive record constructors (unit).
  | StronglyRigid     -- ^ Under at least one and only inductive constructors.
  deriving (Eq, Show, Functor, Foldable)

type FlexRig = FlexRig' MetaSet

class LensFlexRig a o | o -> a where
  lensFlexRig :: Lens' (FlexRig' a) o

instance LensFlexRig a (FlexRig' a) where
  lensFlexRig f x = f x

isFlexible :: LensFlexRig a o => o -> Bool
isFlexible o = case o ^. lensFlexRig of
  Flexible {} -> True
  _ -> False

isUnguarded :: LensFlexRig a o => o -> Bool
isUnguarded o = case o ^. lensFlexRig of
  Unguarded -> True
  _ -> False

isWeaklyRigid :: LensFlexRig a o => o -> Bool
isWeaklyRigid o = case o ^. lensFlexRig of
   WeaklyRigid -> True
   _ -> False

isStronglyRigid :: LensFlexRig a o => o -> Bool
isStronglyRigid o = case o ^. lensFlexRig of
  StronglyRigid -> True
  _ -> False

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
composeFlexRig = curry $ \case
    (Flexible ms1, Flexible ms2) -> Flexible $ ms1 <> ms2
    (Flexible ms1, _) -> Flexible ms1
    (_, Flexible ms2) -> Flexible ms2
    (WeaklyRigid, _) -> WeaklyRigid
    (_, WeaklyRigid) -> WeaklyRigid
    (StronglyRigid, _) -> StronglyRigid
    (_, StronglyRigid) -> StronglyRigid
    (Unguarded, Unguarded) -> Unguarded

-- | Unit for 'composeFlexRig'.
oneFlexRig :: FlexRig' a
oneFlexRig = Unguarded

---------------------------------------------------------------------------
-- * Multi-dimensional feature vector for variable occurrence (semigroup)

-- | Occurrence of free variables is classified by several dimensions.
--   Currently, we have 'FlexRig' and 'Modality'.
data VarOcc' a = VarOcc
  { varFlexRig   :: FlexRig' a
  , varModality  :: Modality
  }
  deriving (Show)
type VarOcc = VarOcc' MetaSet

-- | Equality up to origin.
instance Eq a => Eq (VarOcc' a) where
  VarOcc fr m == VarOcc fr' m' = fr == fr' && sameModality m m'

instance LensModality (VarOcc' a) where
  getModality = varModality
  mapModality f (VarOcc x r) = VarOcc x $ f r

instance LensRelevance (VarOcc' a) where
instance LensQuantity (VarOcc' a) where

-- | Access to 'varFlexRig' in 'VarOcc'.
instance LensFlexRig a (VarOcc' a) where
  lensFlexRig f (VarOcc fr m) = f fr <&> \ fr' -> VarOcc fr' m
-- lensFlexRig :: Lens' (FlexRig' a) (VarOcc' a)
-- lensFlexRig f (VarOcc fr m) = f fr <&> \ fr' -> VarOcc fr' m


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
  mappend = (<>)

-- | The absorptive element of variable occurrence under aggregation:
--   strongly rigid, relevant.
topVarOcc :: VarOcc' a
topVarOcc = VarOcc StronglyRigid topModality

-- | First argument is the outer occurrence (context) and second is the inner.
--   This multiplicative operation is to modify an occurrence under a context.
composeVarOcc :: Semigroup a => VarOcc' a -> VarOcc' a -> VarOcc' a
composeVarOcc (VarOcc o m) (VarOcc o' m') = VarOcc (composeFlexRig o o') (m <> m')
  -- We use the multipicative modality monoid (composition).

oneVarOcc :: VarOcc' a
oneVarOcc = VarOcc Unguarded mempty

---------------------------------------------------------------------------
-- * Storing variable occurrences (semimodule).

-- | Any representation @c@ of a set of variables need to be able to be modified by
--   a variable occurrence. This is to ensure that free variable analysis is
--   compositional. For instance, it should be possible to compute `fv (v [u/x])`
--   from `fv v` and `fv u`.
--
--   In algebraic terminology, a variable set @a@ needs to be (almost) a left semimodule
--   to the semiring 'VarOcc'.
class (Singleton MetaId a, Semigroup a, Monoid a, Semigroup c, Monoid c) => IsVarSet a c | c -> a where
  -- | Laws
  --    * Respects monoid operations:
  --      ```
  --        withVarOcc o mempty   == mempty
  --        withVarOcc o (x <> y) == withVarOcc o x <> withVarOcc o y
  --      ```
  --    * Respects VarOcc composition:
  --      ```
  --        withVarOcc oneVarOcc             = id
  --        withVarOcc (composeVarOcc o1 o2) = withVarOcc o1 . withVarOcc o2
  --      ```
  --    * Respects VarOcc aggregation:
  --      ```
  --        withVarOcc (o1 <> o2) x = withVarOcc o1 x <> withVarOcc o2 x
  --      ```
  --      Since the corresponding unit law may fail,
  --      ```
  --        withVarOcc mempty x = mempty
  --      ```
  --      it is not quite a semimodule.
  withVarOcc :: VarOcc' a -> c -> c

-- | Representation of a variable set as map from de Bruijn indices
--   to 'VarOcc'.
type TheVarMap' a = IntMap (VarOcc' a)
newtype VarMap' a = VarMap { theVarMap :: TheVarMap' a }
  deriving (Eq, Show)

type TheVarMap = TheVarMap' MetaSet
type    VarMap =    VarMap' MetaSet

-- | A "set"-style 'Singleton' instance with default/initial variable occurrence.
instance Singleton Variable (VarMap' a) where
  singleton i = VarMap $ IntMap.singleton i oneVarOcc

mapVarMap :: (TheVarMap' a -> TheVarMap' b) -> VarMap' a -> VarMap' b
mapVarMap f = VarMap . f . theVarMap

lookupVarMap :: Variable -> VarMap' a -> Maybe (VarOcc' a)
lookupVarMap i = IntMap.lookup i . theVarMap

-- Andreas & Jesper, 2018-05-11, issue #3052:

-- | Proper monoid instance for @VarMap@ rather than inheriting the broken one from IntMap.
--   We combine two occurrences of a variable using 'mappend'.
instance Semigroup a => Semigroup (VarMap' a) where
  VarMap m <> VarMap m' = VarMap $ IntMap.unionWith (<>) m m'

instance Semigroup a => Monoid (VarMap' a) where
  mempty  = VarMap IntMap.empty
  mappend = (<>)
  mconcat = VarMap . IntMap.unionsWith (<>) . map theVarMap
  -- mconcat = VarMap . IntMap.unionsWith mappend . coerce   -- ghc 8.6.5 does not seem to like this coerce

instance (Singleton MetaId a, Semigroup a, Monoid a) => IsVarSet a (VarMap' a) where
  withVarOcc o = mapVarMap $ fmap $ composeVarOcc o


---------------------------------------------------------------------------
-- * Simple flexible/rigid variable collection.

-- | Keep track of 'FlexRig' for every variable, but forget the involved meta vars.
type TheFlexRigMap = IntMap (FlexRig' ())
newtype FlexRigMap = FlexRigMap { theFlexRigMap :: TheFlexRigMap }
  deriving (Show, Singleton (Variable, FlexRig' ()))

mapFlexRigMap :: (TheFlexRigMap -> TheFlexRigMap) -> FlexRigMap -> FlexRigMap
mapFlexRigMap f = FlexRigMap . f . theFlexRigMap

instance Semigroup FlexRigMap where
  FlexRigMap m <> FlexRigMap m' = FlexRigMap $ IntMap.unionWith addFlexRig m m'

instance Monoid FlexRigMap where
  mempty  = FlexRigMap IntMap.empty
  mappend = (<>)
  mconcat = FlexRigMap . IntMap.unionsWith addFlexRig . map theFlexRigMap

-- | Compose everything with the 'varFlexRig' part of the 'VarOcc'.
instance IsVarSet () FlexRigMap where
  withVarOcc o = mapFlexRigMap $ fmap $ composeFlexRig $ () <$ varFlexRig o

instance Singleton MetaId () where
  singleton _ = ()

---------------------------------------------------------------------------
-- * Environment for collecting free variables.

-- | Where should we skip sorts in free variable analysis?

data IgnoreSorts
  = IgnoreNot            -- ^ Do not skip.
  | IgnoreInAnnotations  -- ^ Skip when annotation to a type.
  | IgnoreAll            -- ^ Skip unconditionally.
  deriving (Eq, Show)

-- | The current context.

data FreeEnv' a b c = FreeEnv
  { feExtra     :: !b
    -- ^ Additional context, e.g., whether to ignore free variables in sorts.
  , feFlexRig   :: !(FlexRig' a)
    -- ^ Are we flexible or rigid?
  , feModality  :: !Modality
    -- ^ What is the current relevance and quantity?
  , feSingleton :: Maybe Variable -> c
    -- ^ Method to return a single variable.
  }

type Variable    = Int
type SingleVar c = Variable -> c

type FreeEnv c = FreeEnv' MetaSet IgnoreSorts c

-- | Ignore free variables in sorts.
feIgnoreSorts :: FreeEnv' a IgnoreSorts c -> IgnoreSorts
feIgnoreSorts = feExtra

instance LensFlexRig a (FreeEnv' a b c) where
  lensFlexRig f e = f (feFlexRig e) <&> \ fr -> e { feFlexRig = fr }

instance LensModality (FreeEnv' a b c) where
  getModality = feModality
  mapModality f e = e { feModality = f (feModality e) }

instance LensRelevance (FreeEnv' a b c) where
instance LensQuantity (FreeEnv' a b c) where

-- | The initial context.

initFreeEnv :: Monoid c => b -> SingleVar c -> FreeEnv' a b c
initFreeEnv e sing = FreeEnv
  { feExtra       = e
  , feFlexRig     = Unguarded
  , feModality    = mempty            -- multiplicative monoid
  , feSingleton   = maybe mempty sing
  }

type FreeT a b m c = ReaderT (FreeEnv' a b c) m c
type FreeM a c = Reader (FreeEnv' a IgnoreSorts c) c

-- | Run function for FreeM.
runFreeM :: IsVarSet a c => SingleVar c -> IgnoreSorts -> FreeM a c -> c
runFreeM single i m = runReader m $ initFreeEnv i single

instance (Applicative m, Semigroup c) => Semigroup (FreeT a b m c) where
  (<>) = liftA2 (<>)

instance (Functor m, Applicative m, Monad m, Semigroup c, Monoid c) => Monoid (FreeT a b m c) where
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

-- | Changing the 'FlexRig' context.
underFlexRig :: (MonadReader r m, LensFlexRig a r, Semigroup a, LensFlexRig a o) => o -> m z -> m z
underFlexRig = local . over lensFlexRig . composeFlexRig . view lensFlexRig

-- | What happens to the variables occurring under a constructor?
underConstructor :: (MonadReader r m, LensFlexRig a r, Semigroup a) => ConHead -> m z -> m z
underConstructor (ConHead c i fs) =
  case (i,fs) of
    -- Coinductive (record) constructors admit infinite cycles:
    (CoInductive, _)   -> underFlexRig WeaklyRigid
    -- Inductive constructors do not admit infinite cycles:
    (Inductive, _)    -> underFlexRig StronglyRigid
    -- Ulf, 2019-10-18: Now the termination checker treats inductive recursive records
    -- the same as datatypes, so absense of infinite cycles can be proven in Agda, and thus
    -- the unifier is allowed to do it too. Test case: test/Succeed/Issue1271a.agda
    -- WAS:
    -- -- Inductive record constructors do not admit infinite cycles,
    -- -- but this cannot be proven inside Agda.
    -- -- Thus, unification should not prove it either.
    -- (Inductive, (_:_)) -> id

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
  freeVars' t = case t of
    Var n ts     -> variable n `mappend` do underFlexRig WeaklyRigid $ freeVars' ts
    -- λ is not considered guarding, as
    -- we cannot prove that x ≡ λy.x is impossible.
    Lam _ t      -> freeVars' t
    Lit _        -> mempty
    Def _ ts     -> underFlexRig WeaklyRigid $ freeVars' ts  -- because we are not in TCM
      -- we cannot query whether we are dealing with a data/record (strongly r.)
      -- or a definition by pattern matching (weakly rigid)
      -- thus, we approximate, losing that x = List x is unsolvable
    Con c _ ts   -> underConstructor c $ freeVars' ts
    -- Pi is not guarding, since we cannot prove that A ≡ B → A is impossible.
    -- Even as we do not permit infinite type expressions,
    -- we cannot prove their absence (as Set is not inductive).
    -- Also, this is incompatible with univalence (HoTT).
    Pi a b       -> freeVars' (a,b)
    Sort s       -> freeVars' s
    Level l      -> freeVars' l
    MetaV m ts   -> underFlexRig (Flexible $ singleton m) $ freeVars' ts
    DontCare mt  -> underModality (Modality Irrelevant mempty mempty) $ freeVars' mt
    Dummy{}      -> mempty

instance Free t => Free (Type' t) where
  freeVars' (El s t) =
    ifM ((IgnoreNot ==) <$> asks feIgnoreSorts)
      {- then -} (freeVars' (s, t))
      {- else -} (freeVars' t)

instance Free Sort where
  freeVars' s =
    ifM ((IgnoreAll ==) <$> asks feIgnoreSorts) mempty $ {- else -}
    case s of
      Type a     -> freeVars' a
      Prop a     -> freeVars' a
      Inf        -> mempty
      SizeUniv   -> mempty
      PiSort a s -> underFlexRig (Flexible mempty) (freeVars' $ unDom a) `mappend`
                    underFlexRig WeaklyRigid (freeVars' (getSort a, s))
      UnivSort s -> underFlexRig WeaklyRigid $ freeVars' s
      MetaS x es -> underFlexRig (Flexible $ singleton x) $ freeVars' es
      DefS _ es  -> underFlexRig WeaklyRigid $ freeVars' es
      DummyS{}   -> mempty

instance Free Level where
  freeVars' (Max _ as) = freeVars' as

instance Free PlusLevel where
  freeVars' (Plus _ l)    = freeVars' l

instance Free LevelAtom where
  freeVars' l = case l of
    MetaLevel m vs   -> underFlexRig (Flexible $ singleton m) $ freeVars' vs
    NeutralLevel _ v -> freeVars' v
    BlockedLevel _ v -> freeVars' v
    UnreducedLevel v -> freeVars' v

instance Free t => Free [t]            where
instance Free t => Free (Maybe t)      where
instance Free t => Free (WithHiding t) where

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
  freeVars' (OtherType t) = freeVars' t
  freeVars' (EqualityType s _eq l t a b) = freeVars' (s, l, [t, a, b])
