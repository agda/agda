{-# OPTIONS -cpp #-}

-- | Computing the free variables of a term.
module TypeChecking.Free where

import qualified Data.Set as Set
import Data.Set (Set)

import Syntax.Common
import Syntax.Internal

#include "../undefined.h"

-- | Doesn't go inside metas.
class Free a where
    freeVars :: a -> Set Nat

instance Free Term where
    freeVars t = case ignoreBlocking t of
	Var n ts   -> Set.singleton n `Set.union` freeVars ts
	Lam _ t    -> freeVars t
	Lit _	   -> Set.empty
	Def _ ts   -> freeVars ts
	Con _ ts   -> freeVars ts
	MetaV _ ts -> freeVars ts
	BlockedV b -> __IMPOSSIBLE__

instance Free Type where
    freeVars a = case a of
	Pi a b	   -> freeVars (a,b)
	Fun a b    -> freeVars (a,b)
	El t _	   -> freeVars t
	Sort _	   -> Set.empty
	LamT _	   -> __IMPOSSIBLE__
	MetaT _ as -> freeVars as

instance Free a => Free [a] where
    freeVars xs = Set.unions $ map freeVars xs

instance (Free a, Free b) => Free (a,b) where
    freeVars (x,y) = freeVars x `Set.union` freeVars y

instance Free a => Free (Arg a) where
    freeVars = freeVars . unArg

instance Free a => Free (Abs a) where
    freeVars (Abs _ b) = Set.map (subtract 1) $ Set.delete 0 $ freeVars b

instance Free ClauseBody where
    freeVars (Body t)	= freeVars t
    freeVars (Bind b)	= freeVars b
    freeVars (NoBind b) = freeVars b

freeIn :: Free a => Nat -> a -> Bool
freeIn v t = v `Set.member` freeVars t

