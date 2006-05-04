
module Syntax.Abstract.Views where

import Syntax.Common
import Syntax.Abstract
import Syntax.Info

data AppView = Application Head [Arg Expr]
	     | NonApplication Expr
		-- ^ TODO: if we allow beta-redexes (which we currently do) there could be one here.

data Head = HeadVar NameInfo Name
	  | HeadDef NameInfo QName
	  | HeadCon NameInfo QName

appView :: Expr -> AppView
appView e =
    case e of
	Var i x	      -> Application (HeadVar i x) []
	Def i x	      -> Application (HeadDef i x) []
	Con i x	      -> Application (HeadCon i x) []
	App i h e1 e2 -> apply i (appView e1) (Arg h e2)
	_	      -> NonApplication e
    where
	apply i v arg@(Arg h e') =
	    case v of
		Application hd es -> Application hd $ es ++ [arg]
		NonApplication e  -> NonApplication (App i h e e')

