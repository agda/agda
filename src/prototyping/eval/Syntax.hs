
module Syntax where

import Data.Map (Map)

type Name = String

data Exp = Var Int
	 | Con Name
	 | Def Name
	 | App Exp Exp
	 | Lam Exp

data Pat = ConP Name [Pat]
	 | VarP
	 | WildP

data Clause = Clause [Pat] Exp

type Sig = Map Name [Clause]

data LamView = NoLam Exp
	     | Lams Int Exp

data AppView = Apps Exp [Exp]

lamView :: Exp -> LamView
lamView (Lam v) = lam $ lamView v
    where
	lam (NoLam v)  = Lams 1 v
	lam (Lams n v) = Lams (n + 1) v
lamView v	= NoLam v

appView :: Exp -> AppView
appView (App u v) = appView u `app` v
    where
	app (Apps u vs) v = Apps u (vs ++ [v])
appView v	  = Apps v []

apps :: Exp -> [Exp] -> Exp
apps = foldl App
