{-# OPTIONS -fglasgow-exts #-}

-- Remember reductions when pattern matching (huge win)

module DeBruijnCBN2 where

import Data.Maybe
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map

import Syntax

-- Evaluation

raiseFrom :: Int -> Int -> Exp -> Exp
raiseFrom n k e = case e of
    Var m
	| m < n	    -> Var m
	| otherwise -> Var (m + k)
    Con c	    -> Con c
    Def c	    -> Def c
    App s t	    -> App (raiseFrom n k s) (raiseFrom n k t)
    Lam e	    -> Lam $ raiseFrom (n + 1) k e

raise :: Int -> Exp -> Exp
raise = raiseFrom 0

substUnder :: Int -> Exp -> Exp -> Exp
substUnder n u v = case v of
    Var m
	| n == m    -> raise n u
	| m < n	    -> Var m
	| otherwise -> Var (m - 1)
    Con c	    -> Con c
    Def c	    -> Def c
    App s t	    -> App (substUnder n u s) (substUnder n u t)
    Lam t	    -> Lam $ substUnder (n + 1) u t

subst :: Exp -> Exp -> Exp
subst = substUnder 0

substs :: [Exp] -> Exp -> Exp
substs us v = foldr subst v $ zipWith raise [0..] us

data Match a = No | DontKnow | Yes a

instance Monoid a => Monoid (Match a) where
    mempty		       = Yes mempty
    mappend  No	      _	       = No
    mappend  DontKnow _	       = DontKnow
    mappend (Yes _)   No       = No
    mappend (Yes _)   DontKnow = DontKnow
    mappend (Yes x)  (Yes y)   = Yes $ mappend x y

data Reduction a b = NotReduced a | Reduced b

matchDef :: Sig -> [Clause] -> [Exp] -> Reduction [Exp] Exp
matchDef sig []	      vs = NotReduced vs
matchDef sig (c : cs) vs = case m of
    No	     -> matchDef sig cs vs'
    DontKnow -> NotReduced vs'
    Yes v    -> Reduced v
    where
	(m, vs') = match sig c vs

match :: Sig -> Clause -> [Exp] -> (Match Exp, [Exp])
match sig (Clause ps v) vs
    | length vs < nargs = (DontKnow, vs)
    | otherwise		=
	let (m, vs0') = matchPats sig ps vs0
	in  case m of
	    Yes us   -> (Yes $ substs us v `apps` vs1, vs0' ++ vs1)
	    No	     -> (No, vs0' ++ vs1)
	    DontKnow -> (DontKnow, vs0' ++ vs1)
	where
	    nargs     = length ps
	    (vs0,vs1) = splitAt nargs vs

matchPats :: Sig -> [Pat] -> [Exp] -> (Match [Exp], [Exp])
matchPats sig [] [] = (Yes [], [])
matchPats sig (p : ps) (v : vs) =
    let (m, v') = matchPat sig p v
    in	case m of
	No	 -> (No, v' : vs)
	DontKnow -> (DontKnow, v' : vs)
	Yes _	 -> let (ms, vs') = matchPats sig ps vs
		    in  (mappend m ms, v' : vs')

matchPat :: Sig -> Pat -> Exp -> (Match [Exp], Exp)
matchPat _ VarP v	   = (Yes [v], v)
matchPat _ WildP v	   = (Yes [v], v)
matchPat sig (ConP c ps) v = case appView v' of
    Apps (Con c') vs
	| c == c'   ->
	    let (m, vs') = matchPats sig ps vs
	    in case m of
		Yes vs	 -> (Yes vs, Con c' `apps` vs')
		No	 -> (No, Con c' `apps` vs')
		DontKnow -> (DontKnow, Con c' `apps` vs')
	| otherwise -> (No, v')
    _		    -> (DontKnow, v')
    where
	v' = whnf sig v

iota :: Sig -> String -> [Exp] -> Exp
iota sig c vs = fromMaybe (Con c `apps` vs) $ do
    cs <- Map.lookup c sig
    case matchDef sig cs vs of
	NotReduced vs -> return $ Con c `apps` vs
	Reduced v     -> return $ whnf sig v

whnf :: Sig -> Exp -> Exp
whnf sig v = case appView v of
    Var n `Apps` vs -> Var n `apps` vs
    Con c `Apps` vs -> Con c `apps` vs
    Def c `Apps` vs -> iota sig c vs
    Lam u `Apps` (v : vs) -> whnf sig (subst v u `apps` vs)
    Lam u `Apps` []	  -> Lam u

eval :: Sig -> Exp -> Exp
eval sig v = case whnf sig v of
    Lam u   -> Lam $ eval sig u
    App u v -> App (eval sig u) (eval sig v)
    u	    -> u
