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
import Data.Semigroup (Semigroup, Monoid, (<>), mempty, mappend, mconcat)
import Data.Set (Set)

import Agda.Syntax.Common
import Agda.Syntax.Internal

-- import Agda.TypeChecking.Irrelevance

import Agda.Utils.Functor
import Agda.Utils.Monad
import Agda.Utils.Singleton
import Agda.Utils.Size

type MetaSet = Set MetaId

-- | Depending on the surrounding context of a variable,
--   it's occurrence can be classified as flexible or rigid,
--   with finer distinctions.
--
--   The constructors are listed in increasing order (wrt. information content).
data FlexRig
  = Flexible MetaSet  -- ^ In arguments of metas.
  | WeaklyRigid       -- ^ In arguments to variables and definitions.
  | Unguarded         -- ^ In top position, or only under inductive record constructors.
  | StronglyRigid     -- ^ Under at least one and only inductive constructors.
  deriving (Eq, Ord, Show)

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
    (Flexible ms1, Flexible ms2) -> Flexible $ ms1 `mappend` ms2
    (Flexible ms1, _) -> Flexible ms1
    (_, Flexible ms2) -> Flexible ms2
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
botVarOcc = VarOcc (Flexible mempty) Irrelevant

-- | First argument is the outer occurrence and second is the inner.
composeVarOcc :: VarOcc -> VarOcc -> VarOcc
composeVarOcc (VarOcc o r) (VarOcc o' r') = VarOcc (composeFlexRig o o') (max r r')

-- | Any representation of a set of variables need to be able to be modified by
--   a variable occurrence. This is to ensure that free variable analysis is
--   compositional. For instance, it should be possible to compute `fv (v [u/x])`
--   from `fv v` and `fv u`.
class (Semigroup a, Monoid a) => IsVarSet a where
  -- | Laws
  --    * Respects monoid operations:
  --      ```
  --        withVarOcc o mempty   == mempty
  --        withVarOcc o (x <> y) == withVarOcc o x <> withVarOcc o y
  --      ```
  --    * Respects VarOcc composition
  --      ```
  --        withVarOcc (composeVarOcc o1 o2) = withVarOcc o1 . withVarOcc o2
  --      ```
  withVarOcc :: VarOcc -> a -> a

type VarMap = IntMap VarOcc

instance IsVarSet VarMap where
  withVarOcc o = fmap (composeVarOcc o)

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
  , feRelevance     :: !Relevance
    -- ^ What is the current relevance?
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
  , feRelevance   = Relevant
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
  r <- asks feRelevance
  s <- asks feSingleton
  pure $ withVarOcc (VarOcc o r) (s $ Just n)

-- | Subtract, but return Nothing if result is negative.
subVar :: Int -> Maybe Variable -> Maybe Variable
subVar n x = x >>= \ i -> (i - n) <$ guard (n <= i)

-- | Going under a binder.
bind :: FreeM a -> FreeM a
bind = bind' 1

bind' :: Nat -> FreeM a -> FreeM a
bind' n = local $ \ e -> e { feSingleton = feSingleton e . subVar n }

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
    DontCare mt  -> goRel Irrelevant $ freeVars' mt
    Shared p     -> freeVars' (derefPtr p)

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
      Prop       -> mempty
      Inf        -> mempty
      SizeUniv   -> mempty
      DLub s1 s2 -> go WeaklyRigid $ freeVars' (s1, s2)

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

instance Free a => Free (Elim' a) where
  freeVars' (Apply a) = freeVars' a
  freeVars' (Proj{} ) = mempty
  freeVars' (IApply x y r) = mconcat $ map freeVars' [x,y,r]

instance Free a => Free (Arg a) where
  freeVars' a = goRel (getRelevance a) $ freeVars' $ unArg a

instance Free a => Free (Dom a) where
  freeVars' = freeVars' . unDom

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
  freeVars' (EqualityType s _eq l t a b) = freeVars' s `mappend` freeVars' (l ++ [t, a, b])
