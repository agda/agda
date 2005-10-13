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
    deriving (Typeable)

{-| Makes sure that the top-level constructor of the expression is the correct
    one. Never returns a 'Paren' and if it returns an 'InfixApp' the operator
    is the right one. Note that it only ever rotates the top-level of the
    expression, sub-expressions are not rotated. The function is parameterised
    over how to get the fixity of a name. Throws an 'InfixException' if the
    correct bracketing cannot be deduced.
-}
rotateInfixApp :: (QName -> Fixity) -> Expr -> Expr
rotateInfixApp fixity e =
    case e of
	Paren _ e'  -> rotateInfixApp fixity e'
	InfixApp e1@(InfixApp _ _ _) op e2 ->
	    case rotateInfixApp fixity e1 of
		InfixApp e1a op' e1b
		    | fixity op' `lowerThan` fixity op
			-> InfixApp e1a op' (InfixApp e1b op e2)
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
	_   -> e

