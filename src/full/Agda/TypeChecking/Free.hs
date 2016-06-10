{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}

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

module Agda.TypeChecking.Free
    ( FreeVars(..)
    , Free, Free', FreeV, FreeVS
    , IgnoreSorts(..)
    , runFree , rigidVars, relevantVars, allVars
    , allFreeVars, allRelevantVars, allRelevantVarsIgnoring
    , freeIn, freeInIgnoringSorts, isBinderUsed
    , relevantIn, relevantInIgnoringSortAnn
    , Occurrence(..)
    , occurrence
    , closed
    , freeVars -- only for testing
    , freeVars'
    ) where

import Prelude hiding (null)

import Control.Monad.Reader

import Data.Maybe
import Data.Monoid
import Data.IntSet (IntSet)
import qualified Data.IntSet as Set
import Data.IntMap (IntMap)
import qualified Data.IntMap as Map
import Data.Set (Set)

import qualified Agda.Benchmarking as Bench

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import Agda.Syntax.Internal

import Agda.TypeChecking.Free.Lazy
  ( Free'(..) , FreeEnv(..), initFreeEnv
  , VarOcc(..), IgnoreSorts(..), Variable, SingleVar
  , MetaSet
  )
import qualified Agda.TypeChecking.Free.Lazy as Free

import Agda.Utils.Null
import Agda.Utils.Singleton

type VarSet = IntSet

-- | Free variables of a term, (disjointly) partitioned into strongly and
--   and weakly rigid variables, flexible variables and irrelevant variables.
data FreeVars = FV
  { stronglyRigidVars :: VarSet
    -- ^ Variables under only and at least one inductive constructor(s).
  , unguardedVars     :: VarSet
    -- ^ Variables at top or only under inductive record constructors
    --   λs and Πs.
    --   The purpose of recording these separately is that they
    --   can still become strongly rigid if put under a constructor
    --   whereas weakly rigid ones stay weakly rigid.
  , weaklyRigidVars   :: VarSet
    -- ^ Ordinary rigid variables, e.g., in arguments of variables.
  , flexibleVars      :: IntMap MetaSet
    -- ^ Variables occuring in arguments of metas.
    --   These are only potentially free, depending how the meta variable is instantiated.
    --   The set contains the id's of the meta variables that this variable is an argument to.
  , irrelevantVars    :: VarSet
    -- ^ Variables in irrelevant arguments and under a @DontCare@, i.e.,
    --   in irrelevant positions.
  , unusedVars        :: VarSet
    -- ^ Variables in 'UnusedArg'uments.
  } deriving (Eq, Show)

mapSRV, mapUGV, mapWRV, mapIRV, mapUUV
  :: (VarSet -> VarSet) -> FreeVars -> FreeVars
mapSRV f fv = fv { stronglyRigidVars = f $ stronglyRigidVars fv }
mapUGV f fv = fv { unguardedVars     = f $ unguardedVars     fv }
mapWRV f fv = fv { weaklyRigidVars   = f $ weaklyRigidVars   fv }
mapIRV f fv = fv { irrelevantVars    = f $ irrelevantVars    fv }
mapUUV f fv = fv { unusedVars        = f $ unusedVars        fv }

mapFXV :: (IntMap MetaSet -> IntMap MetaSet) -> FreeVars -> FreeVars
mapFXV f fv = fv { flexibleVars      = f $ flexibleVars      fv }

-- | Rigid variables: either strongly rigid, unguarded, or weakly rigid.
rigidVars :: FreeVars -> VarSet
rigidVars fv = Set.unions
  [ stronglyRigidVars fv
  ,     unguardedVars fv
  ,   weaklyRigidVars fv
  ]

-- | All but the irrelevant variables.
relevantVars :: FreeVars -> VarSet
relevantVars fv = Set.unions [rigidVars fv, Map.keysSet (flexibleVars fv)]

-- | @allVars fv@ includes irrelevant variables.
allVars :: FreeVars -> VarSet
allVars fv = Set.unions [relevantVars fv, irrelevantVars fv, unusedVars fv]

data Occurrence
  = NoOccurrence
  | Irrelevantly
  | StronglyRigid     -- ^ Under at least one and only inductive constructors.
  | Unguarded         -- ^ In top position, or only under inductive record constructors.
  | WeaklyRigid       -- ^ In arguments to variables and definitions.
  | Flexible MetaSet  -- ^ In arguments of metas.
  | Unused
  deriving (Eq,Show)

-- | Compute an occurrence of a single variable in a piece of internal syntax.
occurrence :: FreeV a => Nat -> a -> Occurrence
occurrence x v = occurrenceFV x $ freeVars v

-- | Extract occurrence of a single variable from computed free variables.
occurrenceFV :: Nat -> FreeVars -> Occurrence
occurrenceFV x fv
  | x `Set.member` stronglyRigidVars fv = StronglyRigid
  | x `Set.member` unguardedVars     fv = Unguarded
  | x `Set.member` weaklyRigidVars   fv = WeaklyRigid
  | Just ms <- Map.lookup x (flexibleVars fv) = Flexible ms
  | x `Set.member` irrelevantVars    fv = Irrelevantly
  | x `Set.member` unusedVars        fv = Unused
  | otherwise                           = NoOccurrence

-- | Mark variables as flexible.  Useful when traversing arguments of metas.
flexible :: MetaSet -> FreeVars -> FreeVars
flexible ms fv =
    fv { stronglyRigidVars = Set.empty
       , unguardedVars     = Set.empty
       , weaklyRigidVars   = Set.empty
       , flexibleVars      = Map.unionsWith mappend
                               [ Map.fromSet (const ms) (rigidVars fv)
                               , fmap (mappend ms) (flexibleVars fv) ]
       }

-- | Mark rigid variables as non-strongly.  Useful when traversing arguments of variables.
weakly :: FreeVars -> FreeVars
weakly fv = fv
  { stronglyRigidVars = Set.empty
  , unguardedVars     = Set.empty
  , weaklyRigidVars   = rigidVars fv
  }

-- | Mark unguarded variables as strongly rigid.  Useful when traversing arguments of inductive constructors.
strongly :: FreeVars -> FreeVars
strongly fv = fv
  { stronglyRigidVars = stronglyRigidVars fv `Set.union` unguardedVars fv
  , unguardedVars     = Set.empty
  }

-- | What happens to the variables occurring under a constructor?
underConstructor :: ConHead -> FreeVars -> FreeVars
underConstructor (ConHead c i fs) =
  case (i,fs) of
    -- Coinductive (record) constructors admit infinite cycles:
    (CoInductive, _)   -> weakly
    -- Inductive data constructors do not admit infinite cycles:
    (Inductive, [])    -> strongly
    -- Inductive record constructors do not admit infinite cycles,
    -- but this cannot be proven inside Agda.
    -- Thus, unification should not prove it either.
    (Inductive, (_:_)) -> id

-- | Mark all free variables as irrelevant.
irrelevantly :: FreeVars -> FreeVars
irrelevantly fv = empty { irrelevantVars = allVars fv }

-- | Mark all free variables as unused, except for irrelevant vars.
unused :: FreeVars -> FreeVars
unused fv = empty
  { irrelevantVars = irrelevantVars fv
  , unusedVars     = Set.unions [ rigidVars fv, Map.keysSet (flexibleVars fv), unusedVars fv ]
  }

-- | Pointwise union.
union :: FreeVars -> FreeVars -> FreeVars
union (FV sv1 gv1 rv1 fv1 iv1 uv1) (FV sv2 gv2 rv2 fv2 iv2 uv2) =
  FV (Set.union sv1 sv2) (Set.union gv1 gv2) (Set.union rv1 rv2) (Map.unionWith mappend fv1 fv2) (Set.union iv1 iv2) (Set.union uv1 uv2)

unions :: [FreeVars] -> FreeVars
unions = foldr union empty

instance Null FreeVars where
  empty = FV Set.empty Set.empty Set.empty Map.empty Set.empty Set.empty
  null (FV a b c d e f) = null a && null b && null c && null d && null e && null f

-- | Free variable sets form a monoid under 'union'.
instance Monoid FreeVars where
  mempty  = empty
  mappend = union
  mconcat = unions

-- | @delete x fv@ deletes variable @x@ from variable set @fv@.
delete :: Nat -> FreeVars -> FreeVars
delete n (FV sv gv rv fv iv uv) = FV (Set.delete n sv) (Set.delete n gv) (Set.delete n rv) (Map.delete n fv) (Set.delete n iv) (Set.delete n uv)

instance Singleton Variable FreeVars where
  singleton (i, VarOcc o r) = mod empty where
    mod :: FreeVars -> FreeVars
    mod = case (o, r) of
      (_, Irrelevant) -> mapIRV (Set.insert i)
      (_, UnusedArg ) -> mapUUV (Set.insert i)
      (Free.StronglyRigid, _) -> mapSRV (Set.insert i)
      (Free.Unguarded    , _) -> mapUGV (Set.insert i)
      (Free.WeaklyRigid  , _) -> mapWRV (Set.insert i)
      (Free.Flexible ms  , _) -> mapFXV (Map.insert i ms)

-- * Collecting free variables.

bench :: a -> a
bench = Bench.billToPure [ Bench.Typing , Bench.Free ]

type Free a = Free' a Any
type FreeV a = Free' a FreeVars
type FreeVS a = Free' a VarSet

-- | Doesn't go inside solved metas, but collects the variables from a
-- metavariable application @X ts@ as @flexibleVars@.
{-# SPECIALIZE freeVars :: FreeV a => a -> FreeVars #-}
freeVars :: (Monoid c, Singleton Variable c, Free' a c) => a -> c
freeVars = freeVarsIgnore IgnoreNot

{-# SPECIALIZE freeVarsIgnore :: FreeV a => IgnoreSorts -> a -> FreeVars #-}
freeVarsIgnore :: (Monoid c, Singleton Variable c, Free' a c) => IgnoreSorts -> a -> c
freeVarsIgnore = runFree singleton

-- Specialization to typical monoids
{-# SPECIALIZE runFree :: Free' a Any      => SingleVar Any      -> IgnoreSorts -> a -> Any #-}
{-# SPECIALIZE runFree :: Free' a All      => SingleVar All      -> IgnoreSorts -> a -> All #-}
{-# SPECIALIZE runFree :: Free' a VarSet   => SingleVar VarSet   -> IgnoreSorts -> a -> VarSet #-}
{-# SPECIALIZE runFree :: Free' a FreeVars => SingleVar FreeVars -> IgnoreSorts -> a -> FreeVars #-}
-- Specialization to Term
{-# SPECIALIZE runFree :: SingleVar Any      -> IgnoreSorts -> Term -> Any #-}
{-# SPECIALIZE runFree :: SingleVar All      -> IgnoreSorts -> Term -> All #-}
{-# SPECIALIZE runFree :: SingleVar VarSet   -> IgnoreSorts -> Term -> VarSet #-}
{-# SPECIALIZE runFree :: SingleVar FreeVars -> IgnoreSorts -> Term -> FreeVars #-}
runFree :: (Monoid c, Free' a c) => SingleVar c -> IgnoreSorts -> a -> c
runFree singleton i t = -- bench $  -- Benchmarking is expensive (4% on std-lib)
  freeVars' t `runReader` (initFreeEnv singleton) { feIgnoreSorts = i }

freeIn'' :: Free a => (VarOcc -> Bool) -> IgnoreSorts -> Nat -> a -> Bool
freeIn'' test ig x t =
  getAny $ runFree (\ (y, o) -> Any $ x == y && test o) ig t

-- | @freeIn' = freeIn'' (const True)@
freeIn' :: Free a => IgnoreSorts -> Nat -> a -> Bool
freeIn' ig x t =
  getAny $ runFree (Any . (x ==) . fst) ig t

{-# SPECIALIZE freeIn :: Nat -> Term -> Bool #-}
freeIn :: Free a => Nat -> a -> Bool
freeIn = freeIn' IgnoreNot

freeInIgnoringSorts :: Free a => Nat -> a -> Bool
freeInIgnoringSorts = freeIn' IgnoreAll

freeInIgnoringSortAnn :: Free a => Nat -> a -> Bool
freeInIgnoringSortAnn = freeIn' IgnoreInAnnotations

relevantInIgnoringSortAnn :: Free a => Nat -> a -> Bool
relevantInIgnoringSortAnn = freeIn'' (not . irrelevantOrUnused . varRelevance) IgnoreInAnnotations

relevantIn :: Free a => Nat -> a -> Bool
relevantIn = freeIn'' (not . irrelevantOrUnused . varRelevance) IgnoreAll

-- | Is the variable bound by the abstraction actually used?
isBinderUsed :: Free a => Abs a -> Bool
isBinderUsed NoAbs{}   = False
isBinderUsed (Abs _ x) = 0 `freeIn` x

-- | Is the term entirely closed (no free variables)?
closed :: Free' a All => a -> Bool
closed t = getAll $ runFree (const $ All False) IgnoreNot t

-- | Collect all free variables.
allFreeVars :: Free' a VarSet => a -> VarSet
allFreeVars = runFree (Set.singleton . fst) IgnoreNot

-- | Collect all relevant free variables, possibly ignoring sorts.
allRelevantVarsIgnoring :: Free' a VarSet => IgnoreSorts -> a -> VarSet
allRelevantVarsIgnoring = runFree sg
  where sg (i, VarOcc _ r) = if irrelevantOrUnused r then Set.empty else Set.singleton i

-- | Collect all relevant free variables.
allRelevantVars :: Free' a VarSet => a -> VarSet
allRelevantVars = allRelevantVarsIgnoring IgnoreNot


{- OLD

-- | A single unguarded variable.
singleton :: Nat -> FreeVars
singleton x = empty { unguardedVars = Set.singleton x }

-- * Collecting free variables.

-- | Where should we skip sorts in free variable analysis?
data IgnoreSorts
  = IgnoreNot            -- ^ Do not skip.
  | IgnoreInAnnotations  -- ^ Skip when annotation to a type.
  | IgnoreAll            -- ^ Skip unconditionally.
  deriving (Eq, Show)

data FreeConf = FreeConf
  { fcIgnoreSorts   :: !IgnoreSorts
    -- ^ Ignore free variables in sorts.
  , fcContext       :: !Int
    -- ^ Under how many binders have we stepped?
  }

initFreeConf :: FreeConf
initFreeConf = FreeConf
  { fcIgnoreSorts = IgnoreNot
  , fcContext     = 0
  }

-- | Return type of fold over syntax.
type FreeT = Reader FreeConf FreeVars

instance Monoid FreeT where
  mempty  = pure mempty
  mappend = liftA2 mappend
  mconcat = mconcat <.> sequence

-- | Base case: a variable.
variable :: Int -> FreeT
variable n = do
  m <- (n -) <$> asks fcContext
  if m >= 0 then pure $ singleton m else mempty

-- | Going under a binder.
bind :: FreeT -> FreeT
bind = local $ \ e -> e { fcContext = 1 + fcContext e }

class Free a where
  freeVars'   :: a -> FreeT

instance Free Term where
  freeVars' t = case t of
    Var n ts   -> variable n `mappend` do weakly <$> freeVars' ts
    -- λ is not considered guarding, as
    -- we cannot prove that x ≡ λy.x is impossible.
    Lam _ t    -> freeVars' t
    Lit _      -> mempty
    Def _ ts   -> weakly <$> freeVars' ts  -- because we are not in TCM
      -- we cannot query whether we are dealing with a data/record (strongly r.)
      -- or a definition by pattern matching (weakly rigid)
      -- thus, we approximate, losing that x = List x is unsolvable
    Con c ts   -> underConstructor c <$> freeVars' ts
    -- Pi is not guarding, since we cannot prove that A ≡ B → A is impossible.
    -- Even as we do not permit infinite type expressions,
    -- we cannot prove their absence (as Set is not inductive).
    -- Also, this is incompatible with univalence (HoTT).
    Pi a b     -> freeVars' (a,b)
    Sort s     -> freeVars' s
    Level l    -> freeVars' l
    MetaV _ ts -> flexible <$> freeVars' ts
    DontCare mt -> irrelevantly <$> freeVars' mt
    Shared p    -> freeVars' (derefPtr p)

instance Free Type where
  freeVars' (El s t) =
    ifM ((IgnoreNot ==) <$> asks fcIgnoreSorts)
      {- then -} (freeVars' (s, t))
      {- else -} (freeVars' t)

instance Free Sort where
  freeVars' s =
    ifM ((IgnoreAll ==) <$> asks fcIgnoreSorts) mempty $ {- else -}
    case s of
      Type a     -> freeVars' a
      Prop       -> mempty
      Inf        -> mempty
      SizeUniv   -> mempty
      DLub s1 s2 -> weakly <$> freeVars' (s1, s2)

instance Free Level where
  freeVars' (Max as) = freeVars' as

instance Free PlusLevel where
  freeVars' ClosedLevel{} = mempty
  freeVars' (Plus _ l)    = freeVars' l

instance Free LevelAtom where
  freeVars' l = case l of
    MetaLevel _ vs   -> flexible <$> freeVars' vs
    NeutralLevel _ v -> freeVars' v
    BlockedLevel _ v -> freeVars' v
    UnreducedLevel v -> freeVars' v

instance Free a => Free [a] where
  freeVars' = foldMap freeVars'

instance Free a => Free (Maybe a) where
  freeVars' = foldMap freeVars'

instance (Free a, Free b) => Free (a,b) where
  freeVars' (x,y) = freeVars' x `mappend` freeVars' y

instance Free a => Free (Elim' a) where
  freeVars' (Apply a) = freeVars' a
  freeVars' (Proj{} ) = mempty

instance Free a => Free (Arg a) where
  freeVars' a = f <$> freeVars' (unArg a)
    where f = case getRelevance a of
               Irrelevant -> irrelevantly
               UnusedArg  -> unused
               _          -> id


instance Free a => Free (Dom a) where
  freeVars' = freeVars' . unDom

instance Free a => Free (Abs a) where
  freeVars' (Abs   _ b) = bind $ freeVars' b
  freeVars' (NoAbs _ b) = freeVars' b

instance Free a => Free (Tele a) where
  freeVars' EmptyTel          = mempty
  freeVars' (ExtendTel a tel) = freeVars' (a, tel)

instance Free ClauseBody where
  freeVars' (Body t)   = freeVars' t
  freeVars' (Bind b)   = freeVars' b
  freeVars'  NoBody    = mempty

instance Free Clause where
  freeVars' = freeVars' . clauseBody

bench :: a -> a
bench = Bench.billToPure [ Bench.Typing , Bench.Free ]

-- | Doesn't go inside solved metas, but collects the variables from a
-- metavariable application @X ts@ as @flexibleVars@.
freeVars :: Free a => a -> FreeVars
freeVars t =
  freeVars' t `runReader` initFreeConf

freeVarsIgnore :: Free a => IgnoreSorts -> a -> FreeVars
freeVarsIgnore i t =
  freeVars' t `runReader` initFreeConf{ fcIgnoreSorts = i }

freeIn :: Free a => Nat -> a -> Bool
freeIn v t = bench $
  v `Set.member` allVars (freeVars t)

freeInIgnoringSorts :: Free a => Nat -> a -> Bool
freeInIgnoringSorts v t = bench $
  v `Set.member` allVars (freeVarsIgnore IgnoreAll t)

freeInIgnoringSortAnn :: Free a => Nat -> a -> Bool
freeInIgnoringSortAnn v t = bench $
  v `Set.member` allVars (freeVarsIgnore IgnoreInAnnotations t)

relevantInIgnoringSortAnn :: Free a => Nat -> a -> Bool
relevantInIgnoringSortAnn v t = bench $
  v `Set.member` relevantVars (freeVarsIgnore IgnoreInAnnotations t)

relevantIn :: Free a => Nat -> a -> Bool
relevantIn v t = bench $
  v `Set.member` relevantVars (freeVarsIgnore IgnoreAll t)

-- | Is the variable bound by the abstraction actually used?
isBinderUsed :: Free a => Abs a -> Bool
isBinderUsed NoAbs{}   = False
isBinderUsed (Abs _ x) = 0 `freeIn` x

-- -}
-- -}
-- -}
