
module Agda.TypeChecking.Free.Base where

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

import Agda.Utils.Functor
import Agda.Utils.Lens
import Agda.Utils.List1 (List1)
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Semigroup
import Agda.Utils.Singleton
import Agda.Utils.Size

---------------------------------------------------------------------------
-- * Set of meta variables.

-- | A set of meta variables.  Forms a monoid under union.

newtype MetaSet = MetaSet { theMetaSet :: HashSet MetaId }
  deriving (Eq, Show, Null, Semigroup, Monoid)

instance Singleton MetaId MetaSet where
  singleton = MetaSet . singleton

insertMetaSet :: MetaId -> MetaSet -> MetaSet
insertMetaSet m (MetaSet ms) = MetaSet $ HashSet.insert m ms

foldrMetaSet :: (MetaId -> a -> a) -> a -> MetaSet -> a
foldrMetaSet f e ms = HashSet.foldr f e $ theMetaSet ms

metaSetToBlocker :: MetaSet -> Blocker
metaSetToBlocker ms = unblockOnAny $ foldrMetaSet (Set.insert . unblockOnMeta) Set.empty ms


---------------------------------------------------------------------------
-- * Flexible and rigid occurrences (semigroup)

-- | Depending on the surrounding context of a variable,
--   it's occurrence can be classified as flexible or rigid,
--   with finer distinctions.
--
--   The constructors are listed in increasing order (wrt. information content).
data FlexRig' a
  = Flexible !a       -- ^ In arguments of metas.
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

class LensFlexRig o a | o -> a where
  lensFlexRig :: Lens' o (FlexRig' a)

instance LensFlexRig (FlexRig' a) a where
  lensFlexRig = id

isFlexible :: LensFlexRig o a => o -> Bool
isFlexible o = case o ^. lensFlexRig of
  Flexible {} -> True
  _ -> False

isUnguarded :: LensFlexRig o a => o -> Bool
isUnguarded o = case o ^. lensFlexRig of
  Unguarded -> True
  _ -> False

isWeaklyRigid :: LensFlexRig o a => o -> Bool
isWeaklyRigid o = case o ^. lensFlexRig of
   WeaklyRigid -> True
   _ -> False

isStronglyRigid :: LensFlexRig o a => o -> Bool
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
composeFlexRig = curry $ \case
    (Flexible ms1, Flexible ms2) -> Flexible $ ms1 <> ms2
    (Flexible ms1, _) -> Flexible ms1
    (_, Flexible ms2) -> Flexible ms2
    (WeaklyRigid, _) -> WeaklyRigid
    (_, WeaklyRigid) -> WeaklyRigid
    (StronglyRigid, _) -> StronglyRigid
    (_, StronglyRigid) -> StronglyRigid
    (Unguarded, Unguarded) -> Unguarded
{-# SPECIALIZE NOINLINE composeFlexRig :: FlexRig' MetaSet -> FlexRig' MetaSet -> FlexRig' MetaSet #-}
{-# SPECIALIZE NOINLINE composeFlexRig :: FlexRig' () -> FlexRig' () -> FlexRig' () #-}

-- | Unit for 'composeFlexRig'.
oneFlexRig :: FlexRig' a
oneFlexRig = Unguarded

-- | Extract a blocker from an occurrence
flexRigToBlocker :: FlexRig -> Blocker
flexRigToBlocker (Flexible ms) = metaSetToBlocker ms
flexRigToBlocker _ = neverUnblock

---------------------------------------------------------------------------
-- * Multi-dimensional feature vector for variable occurrence (semigroup)

-- | Occurrence of free variables is classified by several dimensions.
--   Currently, we have 'FlexRig' and 'Modality'.
data VarOcc' a = VarOcc
  { varFlexRig   :: !(FlexRig' a)
  , varModality  :: {-# UNPACK #-} !Modality
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
instance LensFlexRig (VarOcc' a) a where
  lensFlexRig f (VarOcc fr m) = f fr <&> \ fr' -> VarOcc fr' m
-- lensFlexRig :: Lens' (VarOcc' a) (FlexRig' a)
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
instance (Monoid a) => Monoid (VarOcc' a) where
  mempty  = VarOcc (Flexible mempty) zeroModality
  mappend = (<>)

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

-- | What's the rigidity of a constructor?
constructorFlexRig :: ConHead -> Elims -> FlexRig' a
constructorFlexRig (ConHead _ _ i fs) es = case i of

  -- Coinductive (record) constructors admit infinite cycles:
  CoInductive -> WeaklyRigid
  -- Inductive constructors do not admit infinite cycles:
  Inductive   | size es == size fs -> StronglyRigid
              | otherwise          -> WeaklyRigid
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
-- * Storing variable occurrences (semimodule).

-- | Any representation @c@ of a set of variables need to be able to be modified by
--   a variable occurrence. This is to ensure that free variable analysis is
--   compositional. For instance, it should be possible to compute `fv (v [u/x])`
--   from `fv v` and `fv u`.
--
--   In algebraic terminology, a variable set @a@ needs to be (almost) a left semimodule
--   to the semiring 'VarOcc'.
class (Singleton MetaId a, Monoid a, Monoid c) => IsVarSet a c | c -> a where
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

instance (Singleton MetaId a, Monoid a) => IsVarSet a (VarMap' a) where
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
-- * Plain variable occurrence counting.

newtype VarCounts = VarCounts { varCounts :: IntMap Int }
  deriving (Eq, Show)

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
  , feSingleton :: !(Maybe Variable -> c)
    -- ^ Method to return a single variable.
  }

type Variable    = Int
type SingleVar c = Variable -> c

type FreeEnv c = FreeEnv' MetaSet IgnoreSorts c

-- | Ignore free variables in sorts.
feIgnoreSorts :: FreeEnv' a IgnoreSorts c -> IgnoreSorts
feIgnoreSorts = feExtra

instance LensFlexRig (FreeEnv' a b c) a where
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
  , feModality    = unitModality      -- multiplicative monoid
  , feSingleton   = maybe mempty sing
  }
