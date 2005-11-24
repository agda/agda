{-# OPTIONS -fglasgow-exts #-}
{-| An info object contains additional information about a piece of abstract
    syntax that isn't part of the actual syntax. For instance, it might contain
    the source code posisiton of an expression or the concrete syntax that
    an internal expression originates from.
-}

module Syntax.Info where

import Control.Monad
import Data.Generics hiding (Fixity)

import Syntax.Common
import Syntax.Position
import Syntax.Concrete
import Syntax.Scope

{--------------------------------------------------------------------------
    General explanations
 --------------------------------------------------------------------------}

-- | This type will probably split into several more specialised types (like
--   'NameInfo').
data Info = InCode Range 
          -- ^ the position ('Range') of something
	  | ConcreteExpr Expr
          -- ^ or the 'Concrete.Expr' it came from
	  | ConcreteDecls [Declaration]
          -- ^ or the 'Concrete.Declaration's if it's a declaration
	  | Info :+: Info
          -- ^ explanation concatenation
	  | Duh 
          -- ^ this is a default for development which should disappear
  deriving (Typeable, Data)

instance Show Info where
    show e = "<explanation>"

-- | If an explanation contains a piece of concrete syntax, return this.
getConcreteExpr :: Info -> Maybe Expr
getConcreteExpr e =
    case e of
	ConcreteExpr c	-> return c
	e1 :+: e2	-> mplus (getConcreteExpr e1) (getConcreteExpr e2)
	_		-> mzero


instance HasRange Info where
    getRange (InCode r)	    = r
    getRange (ex1 :+: ex2)  = fuseRange ex1 ex2
    getRange _		    = noRange

{--------------------------------------------------------------------------
    Name explanations
 --------------------------------------------------------------------------}

data NameInfo =
	NameInfo { bindingSite   :: Range
		 , concreteName  :: QName
		 , nameFixity    :: Fixity
		 , nameAccess    :: Access
		 }

{--------------------------------------------------------------------------
    Meta explanations
 --------------------------------------------------------------------------}

data MetaInfo =
	MetaInfo { metaRange	:: Range
		 , metaScope	:: ScopeInfo
		 }

