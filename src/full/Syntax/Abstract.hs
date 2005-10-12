
{-| The abstract syntax. This is what you get after desugaring and scope
    analysis of the concrete syntax. The type checker works on abstract syntax,
    producing internal syntax ("Syntax.Internal").
-}
module Syntax.Abstract
    where

import Syntax.Explanation
import Syntax.Common

data Expr
	= Var Expl Name
	| Def Expl QName
	| Con Expl QName
	| Data Expl QName
	| QuestionMark Expl
	| Underscore Expl
	| App Expl Hiding Expr Expr

