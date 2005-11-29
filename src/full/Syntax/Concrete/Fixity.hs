{-# OPTIONS -fglasgow-exts #-}

{-| The parser doesn't know about fixity declarations and parses all infix
    operators left associatively with the same precedence. This module
    contains the function that rotates infix applications, taking precedence
    information into account.
-}
module Syntax.Concrete.Fixity where

import Control.Exception
import Data.Typeable

import Syntax.Concrete
import Syntax.Position

-- | Thrown by 'rotateInfixApp' if the correct bracketing cannot be deduced.
data InfixException = BadInfixApp Range (QName, Fixity) (QName, Fixity)
    deriving (Typeable, Show)

instance HasRange InfixException where
    getRange (BadInfixApp r _ _) = r

data InfixView e = IVApp e QName e
		 | IVOther e

infixView :: Expr -> InfixView Expr
infixView (InfixApp e1 op e2) = IVApp e1 op e2
infixView e		      = IVOther e

infixViewP :: Pattern -> InfixView Pattern
infixViewP (InfixAppP p op q) = IVApp p op q
infixViewP p		      = IVOther p

{-| Makes sure that the top-level constructor of the expression is the correct
    one. Given an 'InfixApp' it returns an 'InfixApp' and the operator is the
    right one. Note that it only ever rotates the top-level of the expression,
    sub-expressions are not rotated. The function is parameterised over how to
    get the fixity of a name. Throws an 'InfixException' if the correct
    bracketing cannot be deduced. It is parameterised over the type of
    expressions and how to get the fixity of a name.
-}
rotateInfixApp' :: HasRange expr
		   => (expr -> InfixView expr)		-- ^ how to analyse an @expr@
		   -> (expr -> QName -> expr -> expr)	-- ^ how to build an infix application in @expr@
		   -> (QName -> Fixity)			-- ^ how to get the fixity of a name
		   -> expr -> expr
rotateInfixApp' view infixApp fixity e =
    case view e of
	IVApp e1 op e2 ->
	    case view $ rotateInfixApp' view infixApp fixity e1 of
		IVApp e1a op' e1b
		    | fixity op' `lowerThan` fixity op
			-> infixApp e1a op' (infixApp e1b op e2)
		    where
			lowerThan (LeftAssoc _ p1) (LeftAssoc _ p2)	= p1 < p2
			lowerThan (RightAssoc _ p1) (RightAssoc _ p2)	= p1 <= p2
			lowerThan f1 f2
			    | prec f1 == prec f2    =
				throwDyn $ BadInfixApp (fuseRange e1a e2)
						       (op',f1) (op,f2)
			    | otherwise		    = prec f1 < prec f2

			prec (LeftAssoc _ p)	= p
			prec (RightAssoc _ p)	= p
			prec (NonAssoc _ p)	= p

		_   -> e
	IVOther e   -> e

-- | Instantiation of 'rotateInfixApp'' to 'Expr'.
rotateInfixApp :: (QName -> Fixity) -> Expr -> Expr
rotateInfixApp f = rotateInfixApp' infixView InfixApp f

-- | Instantiation of 'rotateInfixApp'' to 'Pattern'.
rotateInfixAppP :: (QName -> Fixity) -> Pattern -> Pattern
rotateInfixAppP f = rotateInfixApp' infixViewP InfixAppP f

