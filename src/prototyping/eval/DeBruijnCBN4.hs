{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}

-- AppView as default, no improvement

module DeBruijnCBN4 where

import Data.Maybe
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Syntax as S
import Syntax ( Pat(..), Name, AppView(..), appView )

data Exp = Var Int [Exp]
	 | Con Name [Exp]
	 | Def Name [Exp]
	 | Lam Exp [Exp]

data Clause = Clause [Pat] Exp

apps :: Exp -> [Exp] -> Exp
apps (Var n es) es' = Var n $ es ++ es'
apps (Con c es) es' = Con c $ es ++ es'
apps (Def c es) es' = Def c $ es ++ es'
apps (Lam e es) es' = Lam e $ es ++ es'

type Sig = Map Name [Clause]

class Compile a c where
    compile :: a -> c

instance Compile a b => Compile (Map k a) (Map k b) where
    compile = fmap compile

instance Compile a b => Compile [a] [b] where
    compile = fmap compile

instance Compile S.Exp Exp where
    compile e = case appView e of
	Apps (S.Var n) es -> Var n	     $ compile es
	Apps (S.Con c) es -> Con c	     $ compile es
	Apps (S.Def c) es -> Def c	     $ compile es
	Apps (S.Lam v) es -> Lam (compile v) $ compile es

instance Compile S.Clause Clause where
    compile (S.Clause ps v) = Clause ps $ compile v

decompile :: Exp -> S.Exp
decompile e = case e of
    Var n es -> S.Var n `S.apps` map decompile es
    Con c es -> S.Con c `S.apps` map decompile es
    Def c es -> S.Def c `S.apps` map decompile es
    Lam e es -> S.Lam (decompile e) `S.apps` map decompile es

-- Evaluation

raiseFrom :: Int -> Int -> Exp -> Exp
raiseFrom n k e = case e of
    Var m es
	| m < n	    -> Var m $ map (raiseFrom n k) es
	| otherwise -> Var (m + k) $ map (raiseFrom n k) es
    Con c es	    -> Con c $ map (raiseFrom n k) es
    Def c es	    -> Def c $ map (raiseFrom n k) es
    Lam e es	    -> Lam (raiseFrom (n + 1) k e) $ map (raiseFrom n k) es

raise :: Int -> Exp -> Exp
raise = raiseFrom 0

subst :: [Exp] -> Exp -> Exp
subst us v = case v of
    Var m es -> (us !! m) `apps` map (subst us) es
    Con c es -> Con c $ map (subst us) es
    Def c es -> Def c $ map (subst us) es
    Lam t es -> Lam (subst (Var 0 [] : map (raise 1) us) t) $ map (subst us) es

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
	let (m, vs0') = {-# SCC "matchPs" #-} matchPats sig ps vs0
	in  case m of
	    Yes us   ->
		let r = {-# SCC "matchYes" #-} subst (reverse us) v `apps` vs1
		in	(Yes r,	   vs0' ++ vs1)
	    No	     -> (No,	   vs0' ++ vs1)
	    DontKnow -> (DontKnow, vs0' ++ vs1)
	where
	    nargs     = {-# SCC "matchLen" #-} length ps
	    (vs0,vs1) = {-# SCC "matchSplit" #-} splitAt nargs vs

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
matchPat sig (ConP c ps) v = case v' of
    Con c' vs
	| c == c'   ->
	    let (m, vs') = matchPats sig ps vs
	    in case m of
		Yes vs	 -> (Yes vs,   Con c' vs')
		No	 -> (No,       Con c' vs')
		DontKnow -> (DontKnow, Con c' vs')
	| otherwise -> (No, v')
    _		    -> (DontKnow, v')
    where
	v' = whnf sig v

iota :: Sig -> String -> [Exp] -> Exp
iota sig c vs = fromMaybe (Con c vs) $ do
    cs <- Map.lookup c sig
    case matchDef sig cs vs of
	NotReduced vs -> return $ Con c vs
	Reduced v     -> return $ whnf sig v

top :: Exp -> [Exp]
top v = v : map (flip Var []) [0..]

whnf :: Sig -> Exp -> Exp
whnf sig v = case v of
    Var n vs	   -> Var n vs
    Con c vs	   -> Con c vs
    Def c vs	   -> iota sig c vs
    Lam u (v : vs) -> whnf sig (subst (top v) u `apps` vs)
    Lam u []	   -> Lam u []

eval' :: Sig -> Exp -> Exp
eval' sig v = case whnf sig v of
    Lam u [] -> Lam (eval' sig u) []
    Var n vs -> Var n $ map (eval' sig) vs
    Con c vs -> Con c $ map (eval' sig) vs
    Def c vs -> Def c $ map (eval' sig) vs

eval :: S.Sig -> S.Exp -> S.Exp
eval sig e = decompile $ eval' (compile sig) (compile e)
