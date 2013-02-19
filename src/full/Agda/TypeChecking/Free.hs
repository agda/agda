{-# LANGUAGE CPP, FlexibleInstances #-}

-- | Computing the free variables of a term.
module Agda.TypeChecking.Free
    ( FreeVars(..)
    , Free
    , freeVars
    , allVars
    , relevantVars
    , rigidVars
    , freeIn, isBinderUsed
    , freeInIgnoringSorts, freeInIgnoringSortAnn
    , relevantIn, relevantInIgnoringSortAnn
    , Occurrence(..)
    , occurrence
    ) where

import qualified Agda.Utils.VarSet as Set
import Agda.Utils.VarSet (VarSet)

import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import Agda.Syntax.Internal

#include "../undefined.h"
import Agda.Utils.Impossible

-- | The distinction between rigid and strongly rigid occurrences comes from:
--   Jason C. Reed, PhD thesis, 2009, page 96 (see also his LFMTP 2009 paper)
--
-- The main idea is that x = t(x) is unsolvable if x occurs strongly rigidly
-- in t.  It might have a solution if the occurrence is not strongly rigid, e.g.
--
--   x = \f -> suc (f (x (\ y -> k)))  has  x = \f -> suc (f (suc k))
--
-- [Jason C. Reed, PhD thesis, page 106]

-- | Free variables of a term, (disjointly) partitioned into strongly and
--   and weakly rigid variables, flexible variables and irrelevant variables.
data FreeVars = FV
  { stronglyRigidVars :: VarSet -- ^ variables at top and under constructors
  , weaklyRigidVars   :: VarSet -- ^ ord. rigid variables, e.g., in arguments of variables
  , flexibleVars      :: VarSet -- ^ variables occuring in arguments of metas. These are potentially free, depending how the meta variable is instantiated.
  , irrelevantVars    :: VarSet -- ^ variables in irrelevant arguments and under a @DontCare@, i.e., in irrelevant positions
  , unusedVars        :: VarSet -- ^ variables in 'UnusedArg'uments
  }

rigidVars :: FreeVars -> VarSet
rigidVars fv = Set.union (stronglyRigidVars fv) (weaklyRigidVars fv)

-- | @allVars fv@ includes irrelevant variables.
allVars :: FreeVars -> VarSet
allVars fv = Set.unions [rigidVars fv, flexibleVars fv, irrelevantVars fv, unusedVars fv]

-- | All but the irrelevant variables.
relevantVars :: FreeVars -> VarSet
relevantVars fv = Set.unions [rigidVars fv, flexibleVars fv]

data Occurrence
  = NoOccurrence
  | Irrelevantly
  | StronglyRigid
  | WeaklyRigid
  | Flexible
  | Unused
  deriving (Eq,Show)

{- NO LONGER
-- | @occurrence x fv@ ignores irrelevant variables in @fv@
-}
occurrence :: Nat -> FreeVars -> Occurrence
occurrence x fv
  | x `Set.member` stronglyRigidVars fv = StronglyRigid
  | x `Set.member` weaklyRigidVars   fv = WeaklyRigid
  | x `Set.member` flexibleVars      fv = Flexible
  | x `Set.member` irrelevantVars    fv = Irrelevantly
  | x `Set.member` unusedVars        fv = Unused
  | otherwise                           = NoOccurrence

-- | Mark variables as flexible.  Useful when traversing arguments of metas.
flexible :: FreeVars -> FreeVars
flexible fv =
    fv { stronglyRigidVars = Set.empty
       , weaklyRigidVars   = Set.empty
       , flexibleVars      = relevantVars fv
       }

-- | Mark rigid variables as non-strongly.  Useful when traversion arguments of variables.
weakly :: FreeVars -> FreeVars
weakly fv = fv
  { stronglyRigidVars = Set.empty
  , weaklyRigidVars   = rigidVars fv
  }

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
union (FV sv1 rv1 fv1 iv1 uv1) (FV sv2 rv2 fv2 iv2 uv2) =
  FV (Set.union sv1 sv2) (Set.union rv1 rv2) (Set.union fv1 fv2) (Set.union iv1 iv2) (Set.union uv1 uv2)

unions :: [FreeVars] -> FreeVars
unions = foldr union empty

empty :: FreeVars
empty = FV Set.empty Set.empty Set.empty Set.empty Set.empty

-- | @delete x fv@ deletes variable @x@ from variable set @fv@.
delete :: Nat -> FreeVars -> FreeVars
delete n (FV sv rv fv iv uv) = FV (Set.delete n sv) (Set.delete n rv) (Set.delete n fv) (Set.delete n iv) (Set.delete n uv)

-- | @subtractFV n fv@ subtracts $n$ from each free variable in @fv@.
subtractFV :: Nat -> FreeVars -> FreeVars
subtractFV n (FV sv rv fv iv uv) = FV (Set.subtract n sv) (Set.subtract n rv) (Set.subtract n fv) (Set.subtract n iv) (Set.subtract n uv)

-- | A single (strongly) rigid variable.
singleton :: Nat -> FreeVars
singleton x = empty { stronglyRigidVars = Set.singleton x }

-- * Collecting free variables.

class Free a where
  freeVars'   :: FreeConf -> a -> FreeVars

-- | Where should we skip sorts in free variable analysis?
data IgnoreSorts
  = IgnoreNot            -- ^ Do not skip.
  | IgnoreInAnnotations  -- ^ Skip when annotation to a type.
  | IgnoreAll            -- ^ Skip unconditionally.
  deriving (Eq, Show)

data FreeConf = FreeConf
  { fcIgnoreSorts   :: IgnoreSorts -- ^ Ignore free variables in sorts.
  }

-- | Doesn't go inside solved metas, but collects the variables from a
-- metavariable application @X ts@ as @flexibleVars@.
freeVars :: Free a => a -> FreeVars
freeVars = freeVars' FreeConf{ fcIgnoreSorts = IgnoreNot }

instance Free Term where
  freeVars' conf t = case t of
    Var n ts   -> singleton n `union` weakly (freeVars' conf ts)
    Lam _ t    -> freeVars' conf t
    Lit _      -> empty
    Def _ ts   -> weakly $ freeVars' conf ts  -- because we are not in TCM
      -- we cannot query whether we are dealing with a data/record (strongly r.)
      -- or a definition by pattern matching (weakly rigid)
      -- thus, we approximate, losing that x = List x is unsolvable
    Con _ ts   -> freeVars' conf ts
    Pi a b     -> freeVars' conf (a,b)
    Sort s     -> freeVars' conf s
    Level l    -> freeVars' conf l
    MetaV _ ts -> flexible $ freeVars' conf ts
    DontCare mt -> irrelevantly $ freeVars' conf mt
    Shared p    -> freeVars' conf (derefPtr p)

instance Free Type where
  freeVars' conf (El s t)
    | fcIgnoreSorts conf == IgnoreNot = freeVars' conf (s, t)
    | otherwise                       = freeVars' conf t

instance Free Sort where
  freeVars' conf s
    | fcIgnoreSorts conf == IgnoreAll = empty
    | otherwise                       = case s of
      Type a     -> freeVars' conf a
      Prop       -> empty
      Inf        -> empty
      DLub s1 s2 -> weakly $ freeVars' conf (s1, s2)

instance Free Level where
  freeVars' conf (Max as) = freeVars' conf as

instance Free PlusLevel where
  freeVars' conf ClosedLevel{} = empty
  freeVars' conf (Plus _ l)    = freeVars' conf l

instance Free LevelAtom where
  freeVars' conf l = case l of
    MetaLevel _ vs   -> flexible $ freeVars' conf vs
    NeutralLevel v   -> freeVars' conf v
    BlockedLevel _ v -> freeVars' conf v
    UnreducedLevel v -> freeVars' conf v

instance Free a => Free [a] where
  freeVars' conf = unions . map (freeVars' conf)

instance Free a => Free (Maybe a) where
  freeVars' conf = maybe empty (freeVars' conf)

instance (Free a, Free b) => Free (a,b) where
  freeVars' conf (x,y) = freeVars' conf x `union` freeVars' conf y

instance Free a => Free (Arg a) where
  freeVars' conf a = f $ freeVars' conf $ unArg a
    where f = case argRelevance a of
               Irrelevant -> irrelevantly
               UnusedArg  -> unused
               _          -> id


instance Free a => Free (Dom a) where
  freeVars' conf = freeVars' conf . unDom

instance Free a => Free (Abs a) where
  freeVars' conf (Abs   _ b) = subtractFV 1 $ delete 0 $ freeVars' conf b
  freeVars' conf (NoAbs _ b) = freeVars' conf b

instance Free a => Free (Tele a) where
  freeVars' conf EmptyTel	   = empty
  freeVars' conf (ExtendTel a tel) = freeVars' conf (a, tel)

instance Free ClauseBody where
  freeVars' conf (Body t)   = freeVars' conf t
  freeVars' conf (Bind b)   = freeVars' conf b
  freeVars' conf  NoBody    = empty

freeIn :: Free a => Nat -> a -> Bool
freeIn v t = v `Set.member` allVars (freeVars t)

freeInIgnoringSorts :: Free a => Nat -> a -> Bool
freeInIgnoringSorts v t =
  v `Set.member` allVars (freeVars' FreeConf{ fcIgnoreSorts = IgnoreAll } t)

freeInIgnoringSortAnn :: Free a => Nat -> a -> Bool
freeInIgnoringSortAnn v t =
  v `Set.member` allVars (freeVars' FreeConf{ fcIgnoreSorts = IgnoreInAnnotations } t)

relevantInIgnoringSortAnn :: Free a => Nat -> a -> Bool
relevantInIgnoringSortAnn v t =
  v `Set.member` relevantVars (freeVars' FreeConf{ fcIgnoreSorts = IgnoreInAnnotations } t)

relevantIn :: Free a => Nat -> a -> Bool
relevantIn v t = v `Set.member` relevantVars (freeVars' FreeConf{ fcIgnoreSorts = IgnoreAll } t)

-- | Is the variable bound by the abstraction actually used?
isBinderUsed :: Free a => Abs a -> Bool
isBinderUsed NoAbs{}   = False
isBinderUsed (Abs _ x) = 0 `freeIn` x
