{-# OPTIONS -cpp #-}

module TypeChecking.Strict where

import Syntax.Common
import Syntax.Internal

#include "../undefined.h"

class Force a where
    force :: a -> Int

instance Force Term where
    force t = case ignoreBlocking t of
	Var _ ts   -> force ts
	Def _ ts   -> force ts
	Con _ ts   -> force ts
	Lam _ t    -> force t
	Lit _	   -> 0
	MetaV _ ts -> force ts
	BlockedV _ -> __IMPOSSIBLE__

instance Force a => Force (Arg a) where
    force = force . unArg

instance Force a => Force [a] where
    force = sum . map force

instance Force a => Force (Abs a) where
    force = force . absBody

infixr 0 $!!

($!!) :: Force a => (a -> b) -> a -> b
f $!! x = force x `seq` f x

