{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}

-- case compilation

module DeBruijnCBN6 where

import Data.List
import Data.Maybe
import Data.Monoid
import Data.Map (Map)
import qualified Data.Map as Map

import qualified Syntax as S
import Syntax ( Pat(..), Name, AppView(..), appView )
import Utils
import Pretty

data Exp = Var Int [Exp]
	 | Con Name [Exp]
	 | Def Name [Exp]
	 | Lam Exp [Exp]

data Case
	= Done Exp
	| Skip Case
	| Bind Case
	| Split (Map Name Case)

apps :: Exp -> [Exp] -> Exp
apps e		[]  = e
apps (Var n es) es' = Var n $ es ++ es'
apps (Con c es) es' = Con c $ es ++ es'
apps (Def c es) es' = Def c $ es ++ es'
apps (Lam e es) es' = Lam e $ es ++ es'

type Sig = Map Name Case

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

instance Compile [S.Clause] Case where
    compile cs = case nextPatterns cs of
	Right [v]   -> Done v
	Right []    -> error $ "no rhs: " ++ show cs
	Right (_:_) -> error $ "overlapping patterns: " ++ show cs
	Left pcs    -> case conOrVar pcs of
	    Left cs   -> Bind $ compile cs
	    Right ccs -> Split $ Map.map compile $ Map.fromList ccs
	where
	    patterns (S.Clause ps     _) = ps
	    body     (S.Clause _      v) = compile v
	    next     (S.Clause (p:ps) v) = (p, S.Clause ps v)

	    nextPatterns :: [S.Clause] -> Either [(Pat, S.Clause)] [Exp]
	    nextPatterns cs
		| all null pss	= Right $ map body cs
		| otherwise	= Left  $ map next cs
		where
		    pss = map patterns cs

	    conOrVar :: [(Pat, S.Clause)] -> Either [S.Clause] [(Name, [S.Clause])]
	    conOrVar cs
		| all (isVar . fst) cs = Left $ map snd cs
		| all (isCon . fst) cs = Right $
		    map splitCon
		    $ groupBy ((==) `on` conName `on` fst)
		    $ sortBy (compare `on` conName `on` fst)
		    $ cs
		| otherwise	       = error $ "bad clauses: " ++ show cs
		where
		    splitCon :: [(Pat, S.Clause)] -> (Name, [S.Clause])
		    splitCon cs = ( conName $ fst $ head cs
				  , map amendClause cs
				  )
			where
			    amendClause (ConP _ ps, S.Clause qs v) = S.Clause (ps ++ qs) v

		    isVar VarP	= True
		    isVar WildP = True
		    isVar _	= False

		    isCon (ConP _ _) = True
		    isCon _	     = False

		    conName (ConP c _ ) = c
		    conArgs (ConP c vs) = vs

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

data Reduction a b = NotReduced a | Reduced b

matchDef :: Sig -> Case -> [Exp] -> Reduction [Exp] Exp
matchDef sig c vs = case match c [] [] vs of
    Reduced v	  -> Reduced v
    NotReduced vs -> NotReduced $ reverse vs
    where
	match (Done v) old sub vs     = Reduced $ subst sub v `apps` vs
	match _	       old sub []     = NotReduced old
	match (Skip c) old sub (v:vs) = match c (v : old) sub vs
	match (Bind c) old sub (v:vs) = match c (v : old) (v : sub) vs
	match (Split m) old sub (v:vs) = case whnf sig v of
	    Con c ws -> case Map.lookup c m of
		Just c'	-> case match c' old sub (ws ++ vs) of
		    Reduced v	  -> Reduced v
		    NotReduced us -> NotReduced $ Con c (reverse us0) : us1
			where (us0, us1) = splitAt (length ws) us
		Nothing	-> NotReduced $ Con c ws : old
	    v -> NotReduced $ v : old

iota :: Sig -> String -> [Exp] -> Exp
iota sig c vs = fromMaybe (Con c vs) $ do
    cs <- {-# SCC "iotaLookup" #-} Map.lookup c sig
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
