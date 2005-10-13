{-# OPTIONS -fglasgow-exts #-}
{-| Explanations describe where a certain thing comes from. For example it might
    indicate the source code position of a particular expression, or give the
    piece of concrete syntax that an internal expression comes from.
-}

module Syntax.Explanation where

import Control.Monad
import Data.Generics

import Syntax.Position
import Syntax.Concrete

-- | Explanations should contain enough information to 
--   reconstruct a derivation
data Expl = InCode Range
	  | DefinedAt Range
	  | ConcreteExpr Expr
	  | ConcreteDecls [Declaration']
	  | Expl :+: Expl
	  | Duh -- ^ this is a default for development which should disappear
  deriving (Typeable, Data)

instance Show Expl where
    show e = "<explanation>"

-- | If an explanation contains a piece of concrete syntax, return this.
getConcreteExpr :: Expl -> Maybe Expr
getConcreteExpr e =
    case e of
	ConcreteExpr c	-> return c
	e1 :+: e2	-> mplus (getConcreteExpr e1) (getConcreteExpr e2)
	_		-> mzero


instance HasRange Expl where
    getRange (InCode r)	    = r
    getRange (ex1 :+: ex2)  = fuseRange ex1 ex2
    getRange _		    = noRange

