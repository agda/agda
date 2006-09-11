{-# OPTIONS -cpp #-}

module Syntax.Strict where

import Data.Generics

import Syntax.Common
import Syntax.Internal
import qualified Syntax.Concrete as C
import Syntax.Interface

#include "../undefined.h"

class Strict a where
    force :: a -> Int

instance Strict Term where
    force t = case ignoreBlocking t of
	Var _ ts   -> force ts
	Def _ ts   -> force ts
	Con _ ts   -> force ts
	Lam _ t    -> force t
	Lit _	   -> 0
	MetaV _ ts -> force ts
	BlockedV _ -> __IMPOSSIBLE__

instance Strict Type where
    force a = case a of
	Pi a b	   -> force (a,b)
	Fun a b    -> force (a,b)
	El t s	   -> force (t,s)
	MetaT _ ts -> force ts
	LamT t	   -> force t
	Sort s	   -> force s

instance Strict Sort where
    force s = case s of
	Type n	  -> n
	Prop	  -> 0
	Lub s1 s2 -> force (s1,s2)
	Suc s	  -> force s
	MetaS _   -> 0

instance Strict ClauseBody where
    force (Body t)   = force t
    force (Bind b)   = force b
    force (NoBind b) = force b

instance Strict C.Expr where
    force e = everything (+) (const 1) e

instance Strict C.Declaration where
    force e = everything (+) (const 1) e

instance Strict C.Pragma where
    force e = everything (+) (const 1) e

instance Strict Interface where
    force e = everything (+) (const 1) e

instance (Strict a, Strict b) => Strict (a,b) where
    force (x,y) = force x + force y

instance Strict a => Strict (Arg a) where
    force = force . unArg

instance Strict a => Strict [a] where
    force = sum . map force

instance Strict a => Strict (Abs a) where
    force = force . absBody

infixr 0 $!!

($!!) :: Strict a => (a -> b) -> a -> b
f $!! x = force x `seq` f x

strict :: Strict a => a -> a
strict x = id $!! x

