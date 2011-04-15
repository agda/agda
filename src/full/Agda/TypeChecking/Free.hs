{-# LANGUAGE CPP #-}

-- | Computing the free variables of a term.
module Agda.TypeChecking.Free
    ( FreeVars(..)
    , Free
    , freeVars
    , allVars
    , rigidVars
    , freeIn
    , freeInIgnoringSorts
    , Occurrence(..)
    , occurrence
    ) where

import qualified Data.Set as Set
import Data.Set (Set)

import Agda.Syntax.Common
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

data FreeVars = FV
  { stronglyRigidVars :: Set Nat -- ^ variables at top and under constructors
  , weaklyRigidVars   :: Set Nat -- ^ ord. rigid variables, e.g., in arguments of variables
  , flexibleVars      :: Set Nat -- ^ variables occuring in arguments of metas. These are potentially free, depending how the meta variable is instantiated.
  }

rigidVars :: FreeVars -> Set Nat
rigidVars fv = Set.union (stronglyRigidVars fv) (weaklyRigidVars fv)

allVars :: FreeVars -> Set Nat
allVars fv = Set.union (rigidVars fv) (flexibleVars fv)

data Occurrence
  = NoOccurrence
  | StronglyRigid
  | WeaklyRigid
  | Flexible
  deriving (Eq,Show)

occurrence :: Nat -> FreeVars -> Occurrence
occurrence x fv | x `Set.member` stronglyRigidVars fv = StronglyRigid
occurrence x fv | x `Set.member` weaklyRigidVars   fv = WeaklyRigid
occurrence x fv | x `Set.member` flexibleVars      fv = Flexible
occurrence _ _ = NoOccurrence

-- | Mark variables as flexible.  Useful when traversing arguments of metas.
flexible :: FreeVars -> FreeVars
flexible fv =
    FV { stronglyRigidVars = Set.empty
       , weaklyRigidVars   = Set.empty
       , flexibleVars      = allVars fv
       }

-- | Mark rigid variables as non-strongly.  Useful when traversion arguments of variables.
weakly :: FreeVars -> FreeVars
weakly fv = fv
  { stronglyRigidVars = Set.empty
  , weaklyRigidVars   = rigidVars fv
  }

-- | Pointwise union.
union :: FreeVars -> FreeVars -> FreeVars
union (FV sv1 rv1 fv1) (FV sv2 rv2 fv2) =
  FV (Set.union sv1 sv2) (Set.union rv1 rv2) (Set.union fv1 fv2)

unions :: [FreeVars] -> FreeVars
unions = foldr union empty

empty :: FreeVars
empty = FV Set.empty Set.empty Set.empty

mapFV :: (Nat -> Nat) -> FreeVars -> FreeVars
mapFV f (FV sv rv fv) = FV (Set.map f sv) (Set.map f rv) (Set.map f fv)

delete :: Nat -> FreeVars -> FreeVars
delete x (FV sv rv fv) =
  FV (Set.delete x sv) (Set.delete x rv) (Set.delete x fv)

-- | A single (strongly) rigid variable.
singleton :: Nat -> FreeVars
singleton x = FV { stronglyRigidVars = Set.singleton x
		 , weaklyRigidVars   = Set.singleton x
		 , flexibleVars      = Set.empty
		 }

-- * Collecting free variables.

class Free a where
  freeVars' :: FreeConf -> a -> FreeVars

data FreeConf = FreeConf
  { fcIgnoreSorts :: Bool
    -- ^ Ignore free variables in sorts.
  }

-- | Doesn't go inside solved metas, but collects the variables from a
-- metavariable application @X ts@ as @flexibleVars@.
freeVars :: Free a => a -> FreeVars
freeVars = freeVars' FreeConf{ fcIgnoreSorts = False }

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
    Fun a b    -> freeVars' conf (a,b)
    Sort s     -> freeVars' conf s
    MetaV _ ts -> flexible $ freeVars' conf ts
    DontCare   -> empty

instance Free Type where
  freeVars' conf (El s t) = freeVars' conf (s, t)

instance Free Sort where
  freeVars' conf s
    | fcIgnoreSorts conf = empty
    | otherwise          = case s of
      Type a     -> freeVars' conf a
      Suc s      -> freeVars' conf s
      Lub s1 s2  -> weakly $ freeVars' conf (s1, s2)
      Prop       -> empty
      Inf        -> empty
      MetaS _ ts -> flexible $ freeVars' conf ts
      DLub s1 s2 -> weakly $ freeVars' conf (s1, s2)

instance Free a => Free [a] where
  freeVars' conf xs = unions $ map (freeVars' conf) xs

instance (Free a, Free b) => Free (a,b) where
  freeVars' conf (x,y) = freeVars' conf x `union` freeVars' conf y

instance Free a => Free (Arg a) where
  freeVars' conf = freeVars' conf . unArg

instance Free a => Free (Abs a) where
  freeVars' conf (Abs _ b) = mapFV (subtract 1) $ delete 0 $ freeVars' conf b

instance Free a => Free (Tele a) where
  freeVars' conf EmptyTel	   = empty
  freeVars' conf (ExtendTel a tel) = freeVars' conf (a, tel)

instance Free ClauseBody where
  freeVars' conf (Body t)   = freeVars' conf t
  freeVars' conf (Bind b)   = freeVars' conf b
  freeVars' conf (NoBind b) = freeVars' conf b
  freeVars' conf  NoBody    = empty

freeIn :: Free a => Nat -> a -> Bool
freeIn v t = v `Set.member` allVars (freeVars t)

freeInIgnoringSorts :: Free a => Nat -> a -> Bool
freeInIgnoringSorts v t =
  v `Set.member` allVars (freeVars' FreeConf{ fcIgnoreSorts = True } t)
