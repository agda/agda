{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

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

import Data.Coerce (coerce)
import Data.Foldable (Foldable, foldMap)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Monoid ( Monoid, mempty, mappend, mconcat )
import Data.Semigroup ( Semigroup, (<>) )
import Data.Set (Set)
import qualified Data.Set as Set

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
  deriving (Eq, Show)
type VarOcc = VarOcc' MetaSet

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

instance Semigroup VarOcc where
  VarOcc o m <> VarOcc o' m' = VarOcc (addFlexRig o o') (addModality m m')

-- | The neutral element for variable occurrence aggregation is least serious
--   occurrence: flexible, irrelevant.
--   This is also the absorptive element for 'composeVarOcc', if we ignore
--   the 'MetaSet' in 'Flexible'.
instance Monoid VarOcc where
  mempty  = VarOcc (Flexible mempty) $ Modality Irrelevant Quantity0
  mappend = (<>)

-- | The absorptive element of variable occurrence under aggregation:
--   strongly rigid, relevant.
topVarOcc :: VarOcc
topVarOcc = VarOcc StronglyRigid $ Modality Relevant Quantityω

-- | First argument is the outer occurrence (context) and second is the inner.
--   This multiplicative operation is to modify an occurrence under a context.
composeVarOcc :: VarOcc -> VarOcc -> VarOcc
composeVarOcc (VarOcc o m) (VarOcc o' m') = VarOcc (composeFlexRig o o') (m <> m')
  -- We use the multipicative modality monoid (composition).

oneVarOcc :: VarOcc
oneVarOcc = VarOcc Unguarded $ Modality Relevant Quantity1

---------------------------------------------------------------------------
-- * Storing variable occurrences (semimodule).

-- | Any representation of a set of variables need to be able to be modified by
--   a variable occurrence. This is to ensure that free variable analysis is
--   compositional. For instance, it should be possible to compute `fv (v [u/x])`
--   from `fv v` and `fv u`.
--
--   In algebraic terminology, a variable set needs to be (almost) a left semimodule
--   to the semiring 'VarOcc'.
class (Semigroup a, Monoid a) => IsVarSet a where
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
  withVarOcc :: VarOcc -> a -> a

-- | Representation of a variable set as map from de Bruijn indices
--   to 'VarOcc'.
type TheVarMap = IntMap VarOcc
newtype VarMap = VarMap { theVarMap :: TheVarMap }
  deriving (Show)

-- | A "set"-style 'Singleton' instance with default/initial variable occurrence.
instance Singleton Variable VarMap where
  singleton i = VarMap $ IntMap.singleton i oneVarOcc

mapVarMap :: (TheVarMap -> TheVarMap) -> VarMap -> VarMap
mapVarMap f = VarMap . f . theVarMap

-- Andreas & Jesper, 2018-05-11, issue #3052:

-- | Proper monoid instance for @VarMap@ rather than inheriting the broken one from IntMap.
--   We combine two occurrences of a variable using 'mappend'.
instance Semigroup VarMap where
  VarMap m <> VarMap m' = VarMap $ IntMap.unionWith mappend m m'

instance Monoid VarMap where
  mempty  = VarMap IntMap.empty
  mappend = (<>)
  mconcat = VarMap . IntMap.unionsWith mappend . map theVarMap
  -- mconcat = VarMap . IntMap.unionsWith mappend . coerce   -- ghc 8.6.5 does not seem to like this coerce

instance IsVarSet VarMap where
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
instance IsVarSet FlexRigMap where
  withVarOcc o = mapFlexRigMap $ fmap $ composeFlexRig $ () <$ varFlexRig o

---------------------------------------------------------------------------
-- * Collecting free variables.

-- | Where should we skip sorts in free variable analysis?

data IgnoreSorts
  = IgnoreNot            -- ^ Do not skip.
  | IgnoreInAnnotations  -- ^ Skip when annotation to a type.
  | IgnoreAll            -- ^ Skip unconditionally.
  deriving (Eq, Show)

-- | The current context.

data FreeEnv c = FreeEnv
  { feIgnoreSorts   :: !IgnoreSorts
    -- ^ Ignore free variables in sorts.
  , feFlexRig       :: !FlexRig
    -- ^ Are we flexible or rigid?
  , feModality     :: !Modality
    -- ^ What is the current relevance and quantity?
  , feSingleton     :: Maybe Variable -> c
    -- ^ Method to return a single variable.
  }

type Variable    = Int
type SingleVar c = Variable -> c

-- | The initial context.

initFreeEnv :: Monoid c => SingleVar c -> FreeEnv c
initFreeEnv sing = FreeEnv
  { feIgnoreSorts = IgnoreNot
  , feFlexRig     = Unguarded
  , feModality    = mempty            -- multiplicative monoid
  , feSingleton   = maybe mempty sing
  }

type FreeM c = Reader (FreeEnv c) c

-- | Run function for FreeM.
runFreeM :: IsVarSet c => SingleVar c -> IgnoreSorts -> FreeM c -> c
runFreeM single i m = runReader m $ (initFreeEnv single) { feIgnoreSorts = i }

instance Semigroup c => Semigroup (FreeM c) where
  (<>) = liftA2 (<>)

instance (Semigroup c, Monoid c) => Monoid (FreeM c) where
  mempty  = pure mempty
  mappend = (<>)
  mconcat = mconcat <.> sequence

-- instance Singleton a c => Singleton a (FreeM c) where
--   singleton = pure . singleton

-- | Base case: a variable.
variable :: IsVarSet c => Int -> FreeM c
variable n = do
  o <- asks feFlexRig
  r <- asks feModality
  s <- asks feSingleton
  pure $ withVarOcc (VarOcc o r) (s $ Just n)

-- | Subtract, but return Nothing if result is negative.
subVar :: Int -> Maybe Variable -> Maybe Variable
-- subVar n x = x >>= \ i -> (i - n) <$ guard (n <= i)
subVar n x = do
  i <- x
  guard $ i >= n
  return $ i - n

-- | Going under a binder.
bind :: FreeM a -> FreeM a
bind = bind' 1

bind' :: Nat -> FreeM a -> FreeM a
bind' n = local $ \ e -> e { feSingleton = feSingleton e . subVar n }

-- | Changing the 'FlexRig' context.
go :: FlexRig -> FreeM a -> FreeM a
go o = local $ \ e -> e { feFlexRig = composeFlexRig o $ feFlexRig e }

-- | Changing the 'Modality'.
goMod :: Modality -> FreeM a -> FreeM a
goMod m = local $ \ e -> e { feModality = composeModality m $ feModality e }

-- | What happens to the variables occurring under a constructor?
underConstructor :: ConHead -> FreeM a -> FreeM a
underConstructor (ConHead c i fs) =
  case (i,fs) of
    -- Coinductive (record) constructors admit infinite cycles:
    (CoInductive, _)   -> go WeaklyRigid
    -- Inductive data constructors do not admit infinite cycles:
    (Inductive, [])    -> go StronglyRigid
    -- Inductive record constructors do not admit infinite cycles,
    -- but this cannot be proven inside Agda.
    -- Thus, unification should not prove it either.
    (Inductive, (_:_)) -> id

-- | Gather free variables in a collection.
class Free a where
  -- Misplaced SPECIALIZE pragma:
  -- {-# SPECIALIZE freeVars' :: a -> FreeM Any #-}
  -- So you cannot specialize all instances in one go. :(
  freeVars' :: IsVarSet c => a -> FreeM c

instance Free Term where
  -- SPECIALIZE instance does not work as well, see
  -- https://ghc.haskell.org/trac/ghc/ticket/10434#ticket
  -- {-# SPECIALIZE instance Free Term All #-}
  -- {-# SPECIALIZE freeVars' :: Term -> FreeM Any #-}
  -- {-# SPECIALIZE freeVars' :: Term -> FreeM All #-}
  -- {-# SPECIALIZE freeVars' :: Term -> FreeM VarSet #-}
  freeVars' t = case t of
    Var n ts     -> variable n `mappend` do go WeaklyRigid $ freeVars' ts
    -- λ is not considered guarding, as
    -- we cannot prove that x ≡ λy.x is impossible.
    Lam _ t      -> freeVars' t
    Lit _        -> mempty
    Def _ ts     -> go WeaklyRigid $ freeVars' ts  -- because we are not in TCM
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
    MetaV m ts   -> go (Flexible $ singleton m) $ freeVars' ts
    DontCare mt  -> goMod (Modality Irrelevant mempty) $ freeVars' mt
    Dummy{}      -> mempty

instance Free a => Free (Type' a) where
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
      -- Jesper, 2019-06-18: Occurrences in the domain of a pi sort
      -- might disappear when instantiation of metavariables causes
      -- the codomain to become non-dependent, so we should count it
      -- as flexible.
      PiSort a s -> go (Flexible empty) (freeVars' $ unDom a) `mappend`
                    go WeaklyRigid (freeVars' (getSort a, s))
      UnivSort s -> go WeaklyRigid $ freeVars' s
      MetaS x es -> go (Flexible $ singleton x) $ freeVars' es
      DefS _ es  -> go WeaklyRigid $ freeVars' es
      DummyS{}   -> mempty

instance Free Level where
  freeVars' (Max as) = freeVars' as

instance Free PlusLevel where
  freeVars' ClosedLevel{} = mempty
  freeVars' (Plus _ l)    = freeVars' l

instance Free LevelAtom where
  freeVars' l = case l of
    MetaLevel m vs   -> go (Flexible $ singleton m) $ freeVars' vs
    NeutralLevel _ v -> freeVars' v
    BlockedLevel _ v -> freeVars' v
    UnreducedLevel v -> freeVars' v

instance Free a => Free [a] where
  freeVars' = foldMap freeVars'

instance Free a => Free (Maybe a) where
  freeVars' = foldMap freeVars'

instance (Free a, Free b) => Free (a, b) where
  freeVars' (x,y) = freeVars' x `mappend` freeVars' y

instance (Free a, Free b, Free c) => Free (a, b, c) where
  freeVars' (x,y,z) = freeVars' x `mappend` freeVars' y `mappend` freeVars' z

instance Free a => Free (Elim' a) where
  freeVars' (Apply a) = freeVars' a
  freeVars' (Proj{} ) = mempty
  freeVars' (IApply x y r) = freeVars' (x,y,r)

instance Free a => Free (Arg a) where
  freeVars' a = goMod (getModality a) $ freeVars' $ unArg a

instance Free a => Free (Dom a) where
  freeVars' d = freeVars' (domTactic d, unDom d)

instance Free a => Free (Abs a) where
  freeVars' (Abs   _ b) = bind $ freeVars' b
  freeVars' (NoAbs _ b) = freeVars' b

instance Free a => Free (Tele a) where
  freeVars' EmptyTel          = mempty
  freeVars' (ExtendTel a tel) = freeVars' (a, tel)

instance Free Clause where
  freeVars' cl = bind' (size $ clauseTel cl) $ freeVars' $ clauseBody cl

instance Free EqualityView where
  freeVars' (OtherType t) = freeVars' t
  freeVars' (EqualityType s _eq l t a b) = freeVars' (s, l, [t, a, b])
