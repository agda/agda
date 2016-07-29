
-- | Computing the free variables of a term.
--
-- This is the old version of ''Agda.TypeChecking.Free'', using
-- 'IntSet's for the separate variable categories.
-- We keep it as a specification.
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

module Agda.TypeChecking.Free.Old
    ( FreeVars(..)
    , Free
    , IgnoreSorts(..)
    , freeVars
    , freeVarsIgnore
    , allVars
    , relevantVars
    , rigidVars
    , freeIn, isBinderUsed
    , freeInIgnoringSorts, freeInIgnoringSortAnn
    , relevantIn, relevantInIgnoringSortAnn
    , Occurrence(..)
    , occurrence
    ) where

import Control.Applicative hiding (empty)
import Control.Monad.Reader

import Data.Foldable (foldMap)
import Data.Semigroup (Semigroup, Monoid, (<>), mempty, mappend, mconcat)

import Agda.Syntax.Common
import Agda.Syntax.Internal

import Agda.Utils.Functor
import Agda.Utils.Monad
import Agda.Utils.Size
import Agda.Utils.VarSet (VarSet)
import qualified Agda.Utils.VarSet as Set

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
  , flexibleVars      :: VarSet
    -- ^ Variables occuring in arguments of metas.
    --   These are only potentially free, depending how the meta variable is instantiated.
  , irrelevantVars    :: VarSet
    -- ^ Variables in irrelevant arguments and under a @DontCare@, i.e.,
    --   in irrelevant positions.
  , unusedVars        :: VarSet
    -- ^ Variables in 'UnusedArg'uments.
  } deriving (Eq, Show)

-- | Rigid variables: either strongly rigid, unguarded, or weakly rigid.
rigidVars :: FreeVars -> VarSet
rigidVars fv = Set.unions
  [ stronglyRigidVars fv
  ,     unguardedVars fv
  ,   weaklyRigidVars fv
  ]

-- | All but the irrelevant variables.
relevantVars :: FreeVars -> VarSet
relevantVars fv = Set.unions [rigidVars fv, flexibleVars fv]

-- | @allVars fv@ includes irrelevant variables.
allVars :: FreeVars -> VarSet
allVars fv = Set.unions [relevantVars fv, irrelevantVars fv, unusedVars fv]

data Occurrence
  = NoOccurrence
  | Irrelevantly
  | StronglyRigid -- ^ Under at least one and only inductive constructors.
  | Unguarded     -- ^ In top position, or only under inductive record constructors.
  | WeaklyRigid   -- ^ In arguments to variables and definitions.
  | Flexible      -- ^ In arguments of metas.
  | Unused
  deriving (Eq,Show)

{- NO LONGER
-- | @occurrence x fv@ ignores irrelevant variables in @fv@
-}
occurrence :: Nat -> FreeVars -> Occurrence
occurrence x fv
  | x `Set.member` stronglyRigidVars fv = StronglyRigid
  | x `Set.member` unguardedVars     fv = Unguarded
  | x `Set.member` weaklyRigidVars   fv = WeaklyRigid
  | x `Set.member` flexibleVars      fv = Flexible
  | x `Set.member` irrelevantVars    fv = Irrelevantly
  | x `Set.member` unusedVars        fv = Unused
  | otherwise                           = NoOccurrence

-- | Mark variables as flexible.  Useful when traversing arguments of metas.
flexible :: FreeVars -> FreeVars
flexible fv =
    fv { stronglyRigidVars = Set.empty
       , unguardedVars     = Set.empty
       , weaklyRigidVars   = Set.empty
       , flexibleVars      = relevantVars fv
       }

-- | Mark rigid variables as non-strongly.  Useful when traversion arguments of variables.
weakly :: FreeVars -> FreeVars
weakly fv = fv
  { stronglyRigidVars = Set.empty
  , unguardedVars     = Set.empty
  , weaklyRigidVars   = rigidVars fv
  }

-- | Mark unguarded variables as strongly rigid.  Useful when traversion arguments of inductive constructors.
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
  , unusedVars     = Set.unions [ rigidVars fv, flexibleVars fv, unusedVars fv ]
  }

-- | Pointwise union.
union :: FreeVars -> FreeVars -> FreeVars
union (FV sv1 gv1 rv1 fv1 iv1 uv1) (FV sv2 gv2 rv2 fv2 iv2 uv2) =
  FV (Set.union sv1 sv2) (Set.union gv1 gv2) (Set.union rv1 rv2) (Set.union fv1 fv2) (Set.union iv1 iv2) (Set.union uv1 uv2)

unions :: [FreeVars] -> FreeVars
unions = foldr union empty

empty :: FreeVars
empty = FV Set.empty Set.empty Set.empty Set.empty Set.empty Set.empty

-- | Free variable sets form a monoid under 'union'.
instance Semigroup FreeVars where
  (<>) = union

instance Monoid FreeVars where
  mempty  = empty
  mappend = (<>)
  mconcat = unions

-- | @delete x fv@ deletes variable @x@ from variable set @fv@.
delete :: Nat -> FreeVars -> FreeVars
delete n (FV sv gv rv fv iv uv) = FV (Set.delete n sv) (Set.delete n gv) (Set.delete n rv) (Set.delete n fv) (Set.delete n iv) (Set.delete n uv)

-- | @subtractFV n fv@ subtracts $n$ from each free variable in @fv@.
subtractFV :: Nat -> FreeVars -> FreeVars
subtractFV n (FV sv gv rv fv iv uv) = FV (Set.subtract n sv) (Set.subtract n gv) (Set.subtract n rv) (Set.subtract n fv) (Set.subtract n iv) (Set.subtract n uv)

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

-- | Doesn't go inside solved metas, but collects the variables from a
-- metavariable application @X ts@ as @flexibleVars@.
freeVars :: Free a => a -> FreeVars
freeVars t = freeVars' t `runReader` initFreeConf

freeVarsIgnore :: Free a => IgnoreSorts -> a -> FreeVars
freeVarsIgnore i t = freeVars' t `runReader` initFreeConf{ fcIgnoreSorts = i }

-- | Return type of fold over syntax.
type FreeT = Reader FreeConf FreeVars

instance Semigroup FreeT where
  (<>) = liftA2 mappend

instance Monoid FreeT where
  mempty  = pure mempty
  mappend = (<>)
  mconcat = mconcat <.> sequence

-- | Base case: a variable.
variable :: Int -> FreeT
variable n = do
  m <- (n -) <$> asks fcContext
  if m >= 0 then pure $ singleton m else mempty

-- | Going under a binder.
bind :: FreeT -> FreeT
bind = bind' 1

-- | Going under n binders.
bind' :: Nat -> FreeT -> FreeT
bind' n = local $ \ e -> e { fcContext = n + fcContext e }

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

instance Free Clause where
  freeVars' cl = bind' (size $ clauseTel cl) $ freeVars' $ clauseBody cl

freeIn :: Free a => Nat -> a -> Bool
freeIn v t = v `Set.member` allVars (freeVars t)

freeInIgnoringSorts :: Free a => Nat -> a -> Bool
freeInIgnoringSorts v t =
  v `Set.member` allVars (freeVarsIgnore IgnoreAll t)

freeInIgnoringSortAnn :: Free a => Nat -> a -> Bool
freeInIgnoringSortAnn v t =
  v `Set.member` allVars (freeVarsIgnore IgnoreInAnnotations t)

relevantInIgnoringSortAnn :: Free a => Nat -> a -> Bool
relevantInIgnoringSortAnn v t =
  v `Set.member` relevantVars (freeVarsIgnore IgnoreInAnnotations t)

relevantIn :: Free a => Nat -> a -> Bool
relevantIn v t = v `Set.member` relevantVars (freeVarsIgnore IgnoreAll t)

-- | Is the variable bound by the abstraction actually used?
isBinderUsed :: Free a => Abs a -> Bool
isBinderUsed NoAbs{}   = False
isBinderUsed (Abs _ x) = 0 `freeIn` x
