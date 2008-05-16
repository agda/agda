{-# OPTIONS -cpp #-}

-- | Computing the free variables of a term.
module TypeChecking.Free 
    ( FreeVars(..)
    , Free(..)
    , allVars
    , freeIn
    ) where

import qualified Data.Set as Set
import Data.Set (Set)

import Syntax.Common
import Syntax.Internal

#include "../undefined.h"
import Utils.Impossible

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
  freeVars :: a -> FreeVars

instance Free Term where
  freeVars t = case ignoreBlocking t of
    Var n ts   -> singleton n `union` freeVars ts
    Lam _ t    -> freeVars t
    Lit _      -> empty
    Def _ ts   -> freeVars ts
    Con _ ts   -> freeVars ts
    Pi a b     -> freeVars (a,b)
    Fun a b    -> freeVars (a,b)
    Sort _     -> empty
    MetaV _ ts -> flexible $ freeVars ts
    BlockedV b -> __IMPOSSIBLE__

instance Free Type where
  freeVars (El _ t) = freeVars t

instance Free a => Free [a] where
  freeVars xs = unions $ map freeVars xs

instance (Free a, Free b) => Free (a,b) where
  freeVars (x,y) = freeVars x `union` freeVars y

instance Free a => Free (Arg a) where
  freeVars = freeVars . unArg

instance Free a => Free (Abs a) where
  freeVars (Abs _ b) = mapFV (subtract 1) $ delete 0 $ freeVars b

instance Free Telescope where
  freeVars EmptyTel	     = empty
  freeVars (ExtendTel a tel) = freeVars (a, tel)

instance Free ClauseBody where
  freeVars (Body t)   = freeVars t
  freeVars (Bind b)   = freeVars b
  freeVars (NoBind b) = freeVars b
  freeVars  NoBody    = empty

freeIn :: Free a => Nat -> a -> Bool
freeIn v t = v `Set.member` allVars (freeVars t)

