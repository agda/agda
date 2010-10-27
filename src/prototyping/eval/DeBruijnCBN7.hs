{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances #-}

-- Int names (IntMap is only marginally faster than Map, so let's go with Map
-- for the time being)

module DeBruijnCBN7 where

import Data.List
import Data.Maybe
import Data.Monoid
import Data.Map (Map, (!))
import Data.Set (Set)
import Data.Trie (Trie)
import qualified Data.Map as Map
import qualified Data.Trie as Trie
import qualified Data.Set as Set

import qualified Syntax as S
import Syntax ( AppView(..), Pat(..), appView )
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
	| Split (NameMap Case)

type Name = Int
type NameMap = Map Name

apps :: Exp -> [Exp] -> Exp
apps e		[]  = e
apps (Var n es) es' = Var n $ es ++ es'
apps (Con c es) es' = Con c $ es ++ es'
apps (Def c es) es' = Def c $ es ++ es'
apps (Lam e es) es' = Lam e $ es ++ es'

type Sig = NameMap Case

class Names a where
    getNames :: a -> Set S.Name

instance Names S.Exp where
    getNames e = case e of
	S.Var _   -> Set.empty
	S.Def c   -> Set.singleton c
	S.Con c   -> Set.singleton c
	S.Lam e   -> getNames e
	S.App u v -> Set.union (getNames u) (getNames v)

instance Names S.Pat where
    getNames p = case p of
	VarP	  -> Set.empty
	WildP	  -> Set.empty
	ConP c ps -> Set.insert c $ getNames ps

instance Names S.Clause where
    getNames (S.Clause ps v) = getNames (ps, v)

instance Names a => Names (Map k a) where
    getNames = getNames . Map.elems

instance Names a => Names [a] where
    getNames = Set.unions . map getNames

instance (Names a, Names b) => Names (a, b) where
    getNames (x, y) = Set.union (getNames x) (getNames y)

class Compile a c | a -> c where
    compile :: a -> c

instance Compile S.Sig (Sig, NameMap S.Name, Map S.Name Name) where
    compile sig = (Map.fromList $ map comp $ Map.toList sig, nameMap, idMap)
	where
	    ns	    = Set.toList $ Set.union (getNames sig) (Set.fromList $ Map.keys sig)
	    nameMap = Map.fromList $ zip [0..] ns
	    idMap   = Map.fromList    $ zip ns [0..]

	    comp (c, cl) = (idMap ! c, compile cl idMap)

instance Compile S.Exp (Map S.Name Name -> Exp) where
    compile e nmap = case appView e of
	Apps (S.Var n) es -> Var n		  $ comps es
	Apps (S.Con c) es -> Con (nmap ! c)	  $ comps es
	Apps (S.Def c) es -> Def (nmap ! c)	  $ comps es
	Apps (S.Lam v) es -> Lam (compile v nmap) $ comps es
	where
	    comps es = map (flip compile nmap) es

instance Compile [S.Clause] (Map S.Name Name -> Case) where
    compile cs nmap = case nextPatterns cs of
	Right [v]   -> Done v
	Right []    -> error $ "no rhs: " ++ show cs
	Right (_:_) -> error $ "overlapping patterns: " ++ show cs
	Left pcs    -> case conOrVar pcs of
	    Left cs   -> Bind $ compile cs nmap
	    Right ccs -> Split $ Map.map (flip compile nmap) $ Map.fromList ccs
	where
	    patterns (S.Clause ps     _) = ps
	    body     (S.Clause _      v) = compile v nmap
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
		    splitCon cs = ( nmap ! conName (fst $ head cs)
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

decompile :: NameMap S.Name -> Exp -> S.Exp
decompile nmap e = case e of
    Var n es -> S.Var n		 `S.apps` map dec es
    Con c es -> S.Con (nmap ! c) `S.apps` map dec es
    Def c es -> S.Def (nmap ! c) `S.apps` map dec es
    Lam e es -> S.Lam (dec e)	 `S.apps` map dec es
    where
	dec = decompile nmap
	(!) = (Map.!)

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
    Var m es -> ({-# SCC "subst!!" #-} us !! m) `apps` map (subst us) es
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

iota :: Sig -> Name -> [Exp] -> Exp
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
eval sig e = decompile nmap $ eval' sig' (compile e imap)
    where
	(sig', nmap, imap) = compile sig
