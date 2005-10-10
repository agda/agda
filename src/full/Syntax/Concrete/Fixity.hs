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

{-| Makes sure that the top-level constructor of the expression is the correct
    one. Never returns a 'Paren' and if it returns an 'InfixApp' the operator
    is the right one. Note that it only ever rotates the top-level of the
    expression, sub-expressions are not rotated. The function is parameterised
    over how to get the fixity of a name. Throws an 'InfixException' if the
    correct bracketing cannot be deduced.
-}
rotateInfixApp :: (QName -> Fixity) -> Expr' local -> Expr' local
rotateInfixApp fixity e =
    case e of
	Paren _ e'  -> rotateInfixApp fixity e'
	InfixApp (InfixApp e1 op' e2) op e3
	    | fixity op' `lowerThan` fixity op
		    -> InfixApp e1 op' (InfixApp e2 op e3)
	    where
		lowerThan (LeftAssoc _ p1) (LeftAssoc _ p2)	= p1 < p2
		lowerThan (RightAssoc _ p1) (RightAssoc _ p2)	= p1 <= p2
		lowerThan f1 f2
		    | prec f1 == prec f2    =
			throwDyn $ BadInfixApp (fuseRange e1 e3)
					       (op',f1) (op,f2)
		    | otherwise		    = prec f1 < prec f2

		prec (LeftAssoc _ p)	= p
		prec (RightAssoc _ p)	= p
		prec (NonAssoc _ p)	= p

	_	    -> e

