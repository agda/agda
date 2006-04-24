
module Syntax where

type Name = String

-- | Invariant: The function must be parametric.
--   Make monadic?
data Abs a = Abs (a -> a)

data Type = Set | El Term | Pi Type (Abs Type)

data Term = Var Int
	  | Con Name
	  | Lam (Abs Term)
	  | App Term Term

data Def = Explicit Name Type Term
	 | Implicit Name Type [Clause]

data Clause = Clause [Name] Pattern Term

-- | Values are type correct, on beta-iota normal form. Variables and
--   definitions are fully applied.
data Value  = VId Name [Value]
	    | VCon Name [Value]
	    | VLam (Abs Value)

