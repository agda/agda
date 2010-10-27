{-# OPTIONS -fglasgow-exts #-}

module DeBruijnCBN where

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

newtype FirstMatch a = FirstMatch { firstMatch :: Match a }
newtype AllMatch a = AllMatch { allMatch :: Match a }

instance Monoid (FirstMatch a) where
    mempty = FirstMatch No
    mappend (FirstMatch No) m       = m
    mappend (FirstMatch DontKnow) _ = FirstMatch DontKnow
    mappend (FirstMatch (Yes v)) _  = FirstMatch $ Yes v

instance Monoid a => Monoid (AllMatch a) where
    mempty					   = AllMatch $ Yes mempty
    mappend (AllMatch No) _			   = AllMatch No
    mappend (AllMatch DontKnow) _		   = AllMatch DontKnow
    mappend (AllMatch (Yes _)) (AllMatch No)	   = AllMatch No
    mappend (AllMatch (Yes _)) (AllMatch DontKnow) = AllMatch DontKnow
    mappend (AllMatch (Yes x)) (AllMatch (Yes y))  = AllMatch $ Yes $ mappend x y

yes :: Match a -> Maybe a
yes (Yes x) = Just x
yes _	    = Nothing

matchDef :: Sig -> [Clause] -> [Exp] -> Maybe Exp
matchDef sig cs vs = yes $ firstMatch $ mconcat $ map (flip (match sig) vs) cs

match :: Sig -> Clause -> [Exp] -> FirstMatch Exp
match sig (Clause ps v) vs
    | length vs < nargs = FirstMatch DontKnow
    | otherwise		= case allMatch $ matchPats sig ps vs0 of
	Yes us	 -> FirstMatch $ Yes $ substs us v `apps` vs1
	No	 -> FirstMatch No
	DontKnow -> FirstMatch DontKnow
	where
	    nargs     = length ps
	    (vs0,vs1) = splitAt nargs vs

matchPats :: Sig -> [Pat] -> [Exp] -> AllMatch [Exp]
matchPats sig ps vs = mconcat $ zipWith (matchPat sig) ps vs

matchPat :: Sig -> Pat -> Exp -> AllMatch [Exp]
matchPat _ VarP v	   = AllMatch $ Yes [v]
matchPat _ WildP v	   = AllMatch $ Yes [v]
matchPat sig (ConP c ps) v = case appView $ whnf sig v of
    Apps (Con c') vs
	| c == c'   -> matchPats sig ps vs
	| otherwise -> AllMatch No
    _		    -> AllMatch DontKnow

iota :: Sig -> String -> [Exp] -> Exp
iota sig c vs = fromMaybe (Con c `apps` vs) $ do
    cs <- Map.lookup c sig
    e  <- matchDef sig cs vs
    return $ whnf sig e

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
