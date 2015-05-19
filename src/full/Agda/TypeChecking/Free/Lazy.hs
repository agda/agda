{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
-- a dependent function type, we check it is actually dependent.
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

module Agda.TypeChecking.Free.Lazy where

import Control.Applicative hiding (empty)
import Control.Monad.Reader

import Data.Foldable (foldMap)
import Data.IntMap (IntMap)
import Data.Monoid

import qualified Agda.Benchmarking as Bench

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import Agda.Syntax.Internal

-- import Agda.TypeChecking.Irrelevance

import Agda.Utils.Function
import Agda.Utils.Functor
import Agda.Utils.Monad
import Agda.Utils.Singleton
import Agda.Utils.VarSet (VarSet)

#include "undefined.h"
import Agda.Utils.Impossible

-- | Depending on the surrounding context of a variable,
--   it's occurrence can be classified as flexible or rigid,
--   with finer distinctions.
--
--   The constructors are listed in increasing order (wrt. information content).
data FlexRig
  = Flexible      -- ^ In arguments of metas.
  | WeaklyRigid   -- ^ In arguments to variables and definitions.
  | Unguarded     -- ^ In top position, or only under inductive record constructors.
  | StronglyRigid -- ^ Under at least one and only inductive constructors.
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | 'FlexRig' composition.  For accumulating the context of a variable.
--
--   'Flexible' is dominant.  Once we are under a meta, we are flexible
--   regardless what else comes.
--
--   'WeaklyRigid' is next in strength.  Destroys strong rigidity.
--
--   'StronglyRigid' is still dominant over 'Unguarded'.
--
--   'Unguarded' is the unit.  It is the top (identity) context.
composeFlexRig :: FlexRig -> FlexRig -> FlexRig
composeFlexRig o o' =
  case (o, o') of
    (Flexible, _) -> Flexible
    (_, Flexible) -> Flexible
    (WeaklyRigid, _) -> WeaklyRigid
    (_, WeaklyRigid) -> WeaklyRigid
    (StronglyRigid, _) -> StronglyRigid
    (_, StronglyRigid) -> StronglyRigid
    (Unguarded, Unguarded) -> Unguarded

-- -- | 'FlexRig' supremum.  Extract the most information about a variable.
-- --
-- --   We make this the default 'Monoid' for 'FlexRig'.
-- instance Monoid FlexRig where
--   mempty  = minBound
--   mappend = max

-- | Occurrence of free variables is classified by several dimensions.
--   Currently, we have 'FlexRig' and 'Relevance'.
data VarOcc = VarOcc
  { varFlexRig   :: FlexRig
  , varRelevance :: Relevance
  }
  deriving (Eq, Show)

-- | When we extract information about occurrence, we care most about
--   about 'StronglyRigid' 'Relevant' occurrences.
maxVarOcc :: VarOcc -> VarOcc -> VarOcc
maxVarOcc (VarOcc o r) (VarOcc o' r') = VarOcc (max o o') (min r r')

topVarOcc :: VarOcc
topVarOcc = VarOcc StronglyRigid Relevant

botVarOcc :: VarOcc
botVarOcc = VarOcc Flexible Irrelevant

type VarMap = IntMap VarOcc

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
  , feBinders       :: !Int
    -- ^ Under how many binders have we stepped?
  , feFlexRig       :: !FlexRig
    -- ^ Are we flexible or rigid?
  , feRelevance     :: !Relevance
    -- ^ What is the current relevance?
  , feSingleton     :: SingleVar c
    -- ^ Method to return a single variable.
  }

type Variable    = (Int, VarOcc)
type SingleVar c = Variable -> c

-- | The initial context.

initFreeEnv :: SingleVar c -> FreeEnv c
initFreeEnv sing = FreeEnv
  { feIgnoreSorts = IgnoreNot
  , feBinders     = 0
  , feFlexRig     = Unguarded
  , feRelevance   = Relevant
  , feSingleton   = sing
  }

type FreeM c = Reader (FreeEnv c) c

instance Monoid c => Monoid (FreeM c) where
  mempty  = pure mempty
  mappend = liftA2 mappend
  mconcat = mconcat <.> sequence

-- instance Singleton a c => Singleton a (FreeM c) where
--   singleton = pure . singleton

-- | Base case: a variable.
variable :: (Monoid c) => Int -> FreeM c
variable n = do
  m <- (n -) <$> asks feBinders
  if m < 0 then mempty else do
    o <- asks feFlexRig
    r <- asks feRelevance
    s <- asks feSingleton
    pure $ s (m, VarOcc o r)

-- | Going under a binder.
bind :: FreeM a -> FreeM a
bind = local $ \ e -> e { feBinders = 1 + feBinders e }

-- | Changing the 'FlexRig' context.
go :: FlexRig -> FreeM a -> FreeM a
go o = local $ \ e -> e { feFlexRig = composeFlexRig o $ feFlexRig e }

-- | Changing the 'Relevance'.
goRel :: Relevance-> FreeM a -> FreeM a
goRel r = local $ \ e -> e { feRelevance = composeRelevance r $ feRelevance e }

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
class Free' a c where
  -- Misplaced SPECIALIZE pragma:
  -- {-# SPECIALIZE freeVars' :: a -> FreeM Any #-}
  -- So you cannot specialize all instances in one go. :(
  freeVars' :: (Monoid c) => a -> FreeM c

instance Free' Term c where
  {-# SPECIALIZE instance Free' Term All #-}
  {-# SPECIALIZE freeVars' :: Term -> FreeM Any #-}
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
    Con c ts     -> underConstructor c $ freeVars' ts
    -- Pi is not guarding, since we cannot prove that A ≡ B → A is impossible.
    -- Even as we do not permit infinite type expressions,
    -- we cannot prove their absence (as Set is not inductive).
    -- Also, this is incompatible with univalence (HoTT).
    Pi a b       -> freeVars' (a,b)
    Sort s       -> freeVars' s
    Level l      -> freeVars' l
    MetaV _ ts   -> go Flexible $ freeVars' ts
    DontCare mt  -> goRel Irrelevant $ freeVars' mt
    Shared p     -> freeVars' (derefPtr p)
    ExtLam cs ts -> freeVars' (cs, ts)

instance Free' Type c where
  {-# SPECIALIZE instance Free' Type All #-}
  {-# SPECIALIZE freeVars' :: Type -> FreeM Any #-}
  freeVars' (El s t) =
    ifM ((IgnoreNot ==) <$> asks feIgnoreSorts)
      {- then -} (freeVars' (s, t))
      {- else -} (freeVars' t)

instance Free' Sort c where
  {-# SPECIALIZE instance Free' Sort All #-}
  {-# SPECIALIZE freeVars' :: Sort -> FreeM Any #-}
  freeVars' s =
    ifM ((IgnoreAll ==) <$> asks feIgnoreSorts) mempty $ {- else -}
    case s of
      Type a     -> freeVars' a
      Prop       -> mempty
      Inf        -> mempty
      SizeUniv   -> mempty
      DLub s1 s2 -> go WeaklyRigid $ freeVars' (s1, s2)

instance Free' Level c where
  {-# SPECIALIZE instance Free' Level All #-}
  {-# SPECIALIZE freeVars' :: Level -> FreeM Any #-}
  freeVars' (Max as) = freeVars' as

instance Free' PlusLevel c where
  {-# SPECIALIZE instance Free' PlusLevel All #-}
  {-# SPECIALIZE freeVars' :: PlusLevel -> FreeM Any #-}
  freeVars' ClosedLevel{} = mempty
  freeVars' (Plus _ l)    = freeVars' l

instance Free' LevelAtom c where
  {-# SPECIALIZE instance Free' LevelAtom All #-}
  {-# SPECIALIZE freeVars' :: LevelAtom -> FreeM Any #-}
  freeVars' l = case l of
    MetaLevel _ vs   -> go Flexible $ freeVars' vs
    NeutralLevel _ v -> freeVars' v
    BlockedLevel _ v -> freeVars' v
    UnreducedLevel v -> freeVars' v

instance Free' a c => Free' [a] c where
  {-# SPECIALIZE instance Free' a All => Free' [a] All #-}
  {-# SPECIALIZE freeVars' :: Free' a Any => [a] -> FreeM Any #-}
  freeVars' = foldMap freeVars'

instance Free' a c => Free' (Maybe a) c where
  {-# SPECIALIZE instance Free' a All => Free' (Maybe a) All #-}
  {-# SPECIALIZE freeVars' :: Free' a Any => Maybe a -> FreeM Any #-}
  freeVars' = foldMap freeVars'

instance (Free' a c, Free' b c) => Free' (a,b) c where
  {-# SPECIALIZE instance (Free' a All, Free' b All) => Free' (a,b) All #-}
  {-# SPECIALIZE freeVars' :: (Free' a Any, Free' b Any) => (a,b) -> FreeM Any #-}
  freeVars' (x,y) = freeVars' x `mappend` freeVars' y

instance Free' a c => Free' (Elim' a) c where
  {-# SPECIALIZE instance Free' a All => Free' (Elim' a) All #-}
  {-# SPECIALIZE freeVars' :: Free' a Any => Elim' a -> FreeM Any #-}
  freeVars' (Apply a) = freeVars' a
  freeVars' (Proj{} ) = mempty

instance Free' a c => Free' (Arg a) c where
  {-# SPECIALIZE instance Free' a All => Free' (Arg a) All #-}
  {-# SPECIALIZE freeVars' :: Free' a Any => Arg a -> FreeM Any #-}
  freeVars' a = goRel (getRelevance a) $ freeVars' $ unArg a

instance Free' a c => Free' (Dom a) c where
  {-# SPECIALIZE instance Free' a All => Free' (Dom a) All #-}
  {-# SPECIALIZE freeVars' :: Free' a Any => Dom a -> FreeM Any #-}
  freeVars' = freeVars' . unDom

instance Free' a c => Free' (Abs a) c where
  {-# SPECIALIZE instance Free' a All => Free' (Abs a) All #-}
  {-# SPECIALIZE freeVars' :: Free' a Any => Abs a -> FreeM Any #-}
  freeVars' (Abs   _ b) = bind $ freeVars' b
  freeVars' (NoAbs _ b) = freeVars' b

instance Free' a c => Free' (Tele a) c where
  {-# SPECIALIZE instance Free' a All => Free' (Tele a) All #-}
  {-# SPECIALIZE freeVars' :: Free' a Any => Tele a -> FreeM Any #-}
  freeVars' EmptyTel          = mempty
  freeVars' (ExtendTel a tel) = freeVars' (a, tel)

instance Free' ClauseBody c where
  {-# SPECIALIZE instance Free' ClauseBody All #-}
  {-# SPECIALIZE freeVars' :: ClauseBody -> FreeM Any #-}
  freeVars' (Body t)   = freeVars' t
  freeVars' (Bind b)   = freeVars' b
  freeVars'  NoBody    = mempty

instance Free' Clause c where
  {-# SPECIALIZE instance Free' Clause All #-}
  {-# SPECIALIZE freeVars' :: Clause -> FreeM Any #-}
  freeVars' = freeVars' . clauseBody

-- -}
