{-# LANGUAGE CPP #-}

-- | Computing the free variables of a term.
module Agda.TypeChecking.Free
    ( FreeVars(..)
    , Free
    , freeVars
    , allVars
    , freeIn
    , freeInIgnoringSorts
    ) where

import qualified Data.Set as Set
import Data.Set (Set)

import Agda.Syntax.Common
import Agda.Syntax.Internal

#include "../undefined.h"
import Agda.Utils.Impossible

data FreeVars = FV { rigidVars	  :: Set Nat
		   , flexibleVars :: Set Nat
		   }

allVars :: FreeVars -> Set Nat
allVars fv = Set.union (rigidVars fv) (flexibleVars fv)

flexible :: FreeVars -> FreeVars
flexible fv =
    FV { rigidVars    = Set.empty
       , flexibleVars = allVars fv
       }

union :: FreeVars -> FreeVars -> FreeVars
union (FV rv1 fv1) (FV rv2 fv2) = FV (Set.union rv1 rv2) (Set.union fv1 fv2)

unions :: [FreeVars] -> FreeVars
unions = foldr union empty

empty :: FreeVars
empty = FV Set.empty Set.empty

mapFV :: (Nat -> Nat) -> FreeVars -> FreeVars
mapFV f (FV rv fv) = FV (Set.map f rv) (Set.map f fv)

delete :: Nat -> FreeVars -> FreeVars
delete x (FV rv fv) = FV (Set.delete x rv) (Set.delete x fv)

singleton :: Nat -> FreeVars
singleton x = FV { rigidVars	= Set.singleton x
		 , flexibleVars = Set.empty
		 }

-- | Doesn't go inside metas.
class Free a where
  freeVars' :: FreeConf -> a -> FreeVars

data FreeConf = FreeConf
  { fcIgnoreSorts :: Bool
    -- ^ Ignore free variables in sorts.
  }

freeVars :: Free a => a -> FreeVars
freeVars = freeVars' FreeConf{ fcIgnoreSorts = False }

instance Free Term where
  freeVars' conf t = case t of
    Var n ts   -> singleton n `union` freeVars' conf ts
    Lam _ t    -> freeVars' conf t
    Lit _      -> empty
    Def _ ts   -> freeVars' conf ts
    Con _ ts   -> freeVars' conf ts
    Pi a b     -> freeVars' conf (a,b)
    Fun a b    -> freeVars' conf (a,b)
    Sort s     -> freeVars' conf s
    MetaV _ ts -> flexible $ freeVars' conf ts

instance Free Type where
  freeVars' conf (El s t) = freeVars' conf (s, t)

instance Free Sort where
  freeVars' conf s
    | fcIgnoreSorts conf = empty
    | otherwise          = case s of
      Type a     -> freeVars' conf a
      Suc s      -> freeVars' conf s
      Lub s1 s2  -> freeVars' conf (s1, s2)
      Prop       -> empty
      Inf        -> empty
      MetaS _ ts -> flexible $ freeVars' conf ts
      DLub s1 s2 -> freeVars' conf (s1, s2)

instance Free a => Free [a] where
  freeVars' conf xs = unions $ map (freeVars' conf) xs

instance (Free a, Free b) => Free (a,b) where
  freeVars' conf (x,y) = freeVars' conf x `union` freeVars' conf y

instance Free a => Free (Arg a) where
  freeVars' conf = freeVars' conf . unArg

instance Free a => Free (Abs a) where
  freeVars' conf (Abs _ b) = mapFV (subtract 1) $ delete 0 $ freeVars' conf b

instance Free Telescope where
  freeVars' conf EmptyTel	     = empty
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

