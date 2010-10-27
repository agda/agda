{-# LANGUAGE CPP #-}

module Agda.Syntax.Strict where

import Data.Generics (everything)

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.Syntax.Parser.Tokens
import qualified Agda.Syntax.Concrete as C
import qualified Agda.Syntax.Concrete.Definitions as C

#include "../undefined.h"
import Agda.Utils.Impossible

-- | @force@ is the recursive @const 0@ function, to force Haskell to evaluate.
class Strict a where
    force :: a -> Int

instance Strict Term where
    force t = case t of
	Var _ ts   -> force ts
	Def _ ts   -> force ts
	Con _ ts   -> force ts
	Lam _ t    -> force t
	Lit _	   -> 0
	Pi a b	   -> force (a,b)
	Fun a b    -> force (a,b)
	Sort s	   -> force s
	MetaV _ ts -> force ts
        DontCare   -> 0

instance Strict Type where
    force (El s t) = force (s,t)

instance Strict Sort where
    force s = case s of
	Type n     -> force n
	Prop       -> 0
	Lub s1 s2  -> force (s1,s2)
	Suc s      -> force s
	MetaS _ as -> force as
        Inf        -> 0
        DLub s1 s2 -> force (s1, s2)

instance Strict ClauseBody where
    force (Body t)   = force t
    force (Bind b)   = force b
    force (NoBind b) = force b
    force  NoBody    = 0

instance Strict C.Expr where
    force e = everything (+) (const 1) e

instance Strict C.Declaration where
    force e = everything (+) (const 1) e

instance Strict C.Pragma where
    force e = everything (+) (const 1) e

instance Strict C.NiceDeclaration where
    force d = everything (+) (const 1) d

instance (Strict a, Strict b) => Strict (a,b) where
    force (x,y) = force x + force y

instance Strict a => Strict (Arg a) where
    force = force . unArg

instance Strict a => Strict [a] where
    force = sum . map force

instance Strict a => Strict (Abs a) where
    force = force . absBody

instance Strict Token where
  -- TODO: This is just a dummy instance. Why can't we just use the
  -- NFData derivation provided by Drift?
  force = (`seq` 0)

infixr 0 $!!

($!!) :: Strict a => (a -> b) -> a -> b
f $!! x = force x `seq` f x

strict :: Strict a => a -> a
strict x = id $!! x
