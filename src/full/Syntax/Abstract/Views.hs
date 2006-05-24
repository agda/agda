
module Syntax.Abstract.Views where

import Syntax.Position
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
	Var i x	     -> Application (HeadVar i x) []
	Def i x	     -> Application (HeadDef i x) []
	Con i x	     -> Application (HeadCon i x) []
	App i e1 arg -> apply i (appView e1) arg
	_	     -> NonApplication e
    where
	apply i v arg =
	    case v of
		Application hd es -> Application hd $ es ++ [arg]
		NonApplication e  -> NonApplication (App i e arg)

instance HasRange Head where
    getRange (HeadVar i _) = getRange i
    getRange (HeadDef i _) = getRange i
    getRange (HeadCon i _) = getRange i

