
module Agda.Syntax.Abstract.Views where

import Agda.Syntax.Position
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import Agda.Syntax.Abstract
import Agda.Syntax.Info

data AppView = Application Expr [NamedArg Expr]
	     -- NonApplication Expr
	     --    -- ^ TODO: if we allow beta-redexes (which we currently do) there could be one here.
             -- 2011-08-24, Dominique: removed..

-- note: everything is an application, possibly of itself to 0 arguments
appView :: Expr -> AppView
appView e =
    case e of
      App i e1 arg        -> apply i (appView e1) arg
      ScopedExpr _ e      -> appView e
      _                   -> Application e []
    where
	apply i v arg =
	    case v of
		Application hd es -> Application hd $ es ++ [arg]

unAppView :: AppView -> Expr
unAppView (Application h es) =
  foldl (App (ExprRange noRange)) h es

-- | Check whether we are dealing with a universe.
isSet :: Expr -> Bool
isSet (ScopedExpr _ e) = isSet e
isSet (App _ e _)      = isSet e
isSet (Set{})          = True
isSet _                = False
