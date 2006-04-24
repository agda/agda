
module Substitution where

import AbsCore
import Value
import Names

-- | Precondition: @rename t (x,y)@ y does not occur in t (either free or
--   bound).
class Rename t where
    rename :: t -> (Ident, Ident) -> t

instance Rename Term where
    rename n (x,y) =
	case n of
	    Var z
		| z == x    -> Var y
		| otherwise -> Var x
	    Lam z n'
		| z == x    -> Lam z n'
		| otherwise -> Lam z $ rename n' (x,y)
	    App n1 n2	    -> rename n1 (x,y) `App` rename n2 (x,y)
	    Set		    -> Set
	    El		    -> El
	    Fun		    -> Fun

-- | @substitute n (x,m) = N(x = M)@
substitute :: Term -> (Ident, Term) -> Term
substitute n (x,m) =
    case n of
	Var y
	    | x == y	-> m
	    | otherwise -> Var y
	Lam y n'
	    | x == y	    -> Lam y n'
	    | y `freeIn` m  -> Lam z $ substitute (rename n' (y,z)) (x,m)
	    | otherwise	    -> Lam y $ substitute n' (x,m)
	    where
		z = freshVar y (allVars $ App n m)

	App n1 n2	  -> substitute n1 (x,m) `App` substitute n2 (x,m)
	Set		  -> Set
	El		  -> El
	Fun		  -> Fun

