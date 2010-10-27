{-# OPTIONS -cpp -fglasgow-exts -fallow-undecidable-instances #-}

-- parent: DeBruijnLazy3

-- keeping track of closed terms
-- another order of magnitude
-- (and we're not even taking care to maintain closedness information)
-- to be fair, the example deals mostly with closed terms

module DeBruijnLazy5 where

import Prelude hiding (mapM)

import Control.Applicative
import Data.Traversable
import Data.List
import Data.Maybe
import Data.Monoid
import Data.Map (Map, (!))
import Data.Set (Set)
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Syntax as S
import Syntax ( AppView(..), Pat(..), appView )
import Utils
import Pretty
import PointerST

#define undefined (error (__FILE__ ++ ":" ++ show __LINE__ ++ ": undefined"))

data ExpR s = Var Int [Exp s]
	    | Con Name [Exp s]
	    | Def Name [Exp s]
	    | Lam (Exp s) [Exp s]
	    | Closed (ExpR s)

type Exp s = Ptr s (ExpR s)

data Case s
	= Done (Exp s)
	| Skip (Case s)
	| Bind (Case s)
	| Split (NameMap (Case s))

type Name = Int
type NameMap = Map Name

type M = HeapM

ignoreClosed (Closed e) = ignoreClosed e
ignoreClosed e		= e

appsR :: ExpR s -> [Exp s] -> ExpR s
appsR e		[]  = e
appsR (Var n es) es' = Var n $ es ++ es'
appsR (Con c es) es' = Con c $ es ++ es'
appsR (Def c es) es' = Def c $ es ++ es'
appsR (Lam e es) es' = Lam e $ es ++ es'
appsR (Closed e) es' = appsR e es'

apps :: Exp s -> [Exp s] -> M s (Exp s)
apps e [] = return e
apps e es = do
    v <- deref e
    alloc (appsR v es)

var n es = alloc (Var n es)
con c es = alloc (Con c es)
def c es = alloc (Def c es)
lam e es = alloc (Lam e es)

type Sig s = NameMap (Case s)

isClosed :: S.Exp -> Bool
isClosed e = closedUnder 0 e
    where
	closedUnder n e = case e of
	    S.Var m -> m < n
	    S.Def _ -> True
	    S.Con _ -> True
	    S.Lam e -> closedUnder (n + 1) e
	    S.App u v -> closedUnder n u && closedUnder n v

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

instance Compile S.Sig (M s (Sig s, NameMap S.Name, Map S.Name Name)) where
    compile sig = do
	sig' <- Map.fromList <$> mapM comp (Map.toList sig)
	return (sig', nameMap, idMap)
	where
	    ns	    = Set.toList $ Set.union (getNames sig) (Set.fromList $ Map.keys sig)
	    nameMap = Map.fromList $ zip [0..] ns
	    idMap   = Map.fromList $ zip ns [0..]

	    comp (c, cl) = do
		cl' <- compile cl idMap
		return (idMap ! c, cl')

instance Compile S.Exp (Map S.Name Name -> M s (Exp s)) where
    compile e nmap = close =<< case appView e of
	Apps (S.Var n) es -> var n	    =<< comps es
	Apps (S.Con c) es -> con (nmap ! c) =<< comps es
	Apps (S.Def c) es -> def (nmap ! c) =<< comps es
	Apps (S.Lam v) es -> do
	    v' <- compile v nmap
	    vs <- comps es
	    lam v' vs
	Apps (S.App _ _) _ -> undefined
	where
	    comps es = mapM (flip compile nmap) es
	    close
		| isClosed e = \v -> do
		    onThunk v (return . Closed)
		    return v
		| otherwise  = return

instance Compile [S.Clause] (Map S.Name Name -> M s (Case s)) where
    compile cs nmap = do
	np <- nextPatterns cs
	case np of
	    Right [v]   -> return $ Done v
	    Right []    -> error $ "no rhs: " ++ show cs
	    Right (_:_) -> error $ "overlapping patterns: " ++ show cs
	    Left pcs    -> case conOrVar pcs of
		Left cs   -> Bind <$> compile cs nmap
		Right ccs -> Split <$> mapM (flip compile nmap) (Map.fromList ccs)
	where
	    patterns (S.Clause ps     _) = ps
	    body     (S.Clause _      v) = compile v nmap
	    next     (S.Clause (p:ps) v) = (p, S.Clause ps v)
	    next     _ = error $ "bad clauses: " ++ show cs

	    nextPatterns :: [S.Clause] -> M s (Either [(Pat, S.Clause)] [Exp s])
	    nextPatterns cs
		| all null pss	= Right <$> mapM body cs
		| otherwise	= return $ Left $ map next cs
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
			    amendClause _ = undefined

		    isVar VarP	= True
		    isVar WildP = True
		    isVar _	= False

		    isCon (ConP _ _) = True
		    isCon _	     = False

		    conName (ConP c _ ) = c
		    conName _ = undefined

		    conArgs (ConP c vs) = vs
		    conArgs _ = undefined

decompile :: NameMap S.Name -> Exp s -> M s S.Exp
decompile nmap e = do
    e <- deref e
    case ignoreClosed e of
	Var n es -> S.apps (S.Var n) <$> mapM dec es
	Con c es -> S.apps (S.Con (nmap ! c)) <$> mapM dec es
	Def c es -> S.apps (S.Def (nmap ! c)) <$> mapM dec es
	Lam e es -> do
	    e <- dec e
	    es <- mapM dec es
	    return $ S.Lam e `S.apps` es
	Closed _ -> undefined
    where
	dec = decompile nmap
	(!) = (Map.!)

-- Evaluation

raiseFrom :: Int -> Int -> Exp s -> M s (Exp s)
raiseFrom n k e = do
    v <- deref e
    case v of
	Var m es
	    | m < n	-> var m =<< mapM (raiseFrom n k) es
	    | otherwise -> var (m + k) =<< mapM (raiseFrom n k) es
	Con c es	-> con c =<< mapM (raiseFrom n k) es
	Def c es	-> def c =<< mapM (raiseFrom n k) es
	Lam e es	-> do
	    e  <- raiseFrom (n + 1) k e
	    es <- mapM (raiseFrom n k) es
	    lam e es
	Closed _ -> return e

raise :: Int -> Exp s -> M s (Exp s)
raise = raiseFrom 0

subst :: [Exp s] -> Exp s -> M s (Exp s)
subst us e = do
    v <- deref e
    case v of
	Var m es -> apps (us !! m) =<< mapM (subst us) es
	Con c es -> con c =<< mapM (subst us) es
	Def c es -> def c =<< mapM (subst us) es
	Lam t es -> do
	    vz	<- var 0 []
	    us' <- mapM (raise 1) us
	    e	<- subst (vz : us') t
	    es	<- mapM (subst us) es
	    lam e es
	Closed _ -> return e

matchDef :: Int -> Sig s -> Case s -> [Exp s] -> M s (Maybe (Exp s))
matchDef ctx sig c vs = match c [] vs
    where
	match (Done v)  sub vs     = {-# SCC "matchDone" #-} Just <$> (flip apps vs =<< subst sub v)
	match _	        sub []     = return Nothing
	match (Skip c)  sub (v:vs) = match c sub vs
	match (Bind c)  sub (v:vs) = match c (v : sub) vs
	match (Split m) sub (v:vs) = do
	    v' <- {-# SCC "matchWHNF" #-} whnf ctx sig v
	    case v' of
		Con c ws -> case {-# SCC "conLookup" #-} Map.lookup c m of
		    Just c' -> match c' sub (ws ++ vs)
		    Nothing -> return Nothing
		_ -> return Nothing

iota :: Int -> Sig s -> Name -> [Exp s] -> M s (ExpR s)
iota ctx sig c vs = case {-# SCC "lookupDef" #-} Map.lookup c sig of
    Nothing -> return $ Con c vs
    Just cs -> do
	mv <- matchDef ctx sig cs vs
	case mv of
	    Nothing -> return $ Con c vs
	    Just v  -> whnf ctx sig v

top :: Int -> Exp s -> M s [Exp s]
top n v = (v :) <$> mapM (flip var []) [0..n - 1]

whnf :: Int -> Sig s -> Exp s -> M s (ExpR s)
whnf ctx sig v = onThunk v $ \v -> case ignoreClosed v of
    Var n vs	   -> return $ Var n vs
    Con c vs	   -> return $ Con c vs
    Def c vs	   -> iota ctx sig c vs
    Lam u (v : vs) -> do
	sub <- top ctx v
	whnf ctx sig =<< flip apps vs =<< subst sub u
    Lam u []	   -> return $ Lam u []
    Closed _ -> undefined

eval' :: Int -> Sig s -> Exp s -> M s ()
eval' ctx sig v = do
    whnf ctx sig v
    onThunk v $ \v -> case ignoreClosed v of
	Lam u []    -> eval' (ctx + 1) sig u >> return v
	Lam u (_:_) -> undefined
	Var n vs    -> mapM (eval' ctx sig) vs >> return v
	Con c vs    -> mapM (eval' ctx sig) vs >> return v
	Def c vs    -> mapM (eval' ctx sig) vs >> return v
	Closed _    -> undefined
    return ()

eval :: S.Sig -> S.Exp -> S.Exp
eval sig e = runHeap (do
	(sig', nmap, imap) <- compile sig
	v <- compile e imap
	eval' 0 sig' v
	decompile nmap v
    )
