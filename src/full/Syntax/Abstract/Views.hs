
module Syntax.Abstract.Views where

import Syntax.Position
import Syntax.Common
import Syntax.Abstract
import Syntax.Info

data AppView = Application Head [NamedArg Expr]
	     | NonApplication Expr
		-- ^ TODO: if we allow beta-redexes (which we currently do) there could be one here.

data Head = HeadVar Name
	  | HeadDef QName
	  | HeadCon [QName]

appView :: Expr -> AppView
appView e =
    case e of
	Var x	       -> Application (HeadVar x) []
	Def x	       -> Application (HeadDef x) []
	Con x	       -> Application (HeadCon x) []
	App i e1 arg   -> apply i (appView e1) arg
	ScopedExpr _ e -> appView e
	_	       -> NonApplication e
    where
	apply i v arg =
	    case v of
		Application hd es -> Application hd $ es ++ [arg]
		NonApplication e  -> NonApplication (App i e arg)

instance HasRange Head where
    getRange (HeadVar x) = getRange x
    getRange (HeadDef x) = getRange x
    getRange (HeadCon x) = getRange x

