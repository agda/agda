{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances -fno-warn-incomplete-patterns #-}

-- keeping track of closed terms in raiseFrom (keep a flag saying whether
-- something happened) turned out to be a bad idea. Eats memory. Might be
-- possible to fix of course...

module DeBruijnLazy4 where

import Prelude hiding (mapM)

import Control.Monad.State hiding (mapM)
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

data ExpR s = Var Int [Exp s]
	    | Con Name [Exp s]
	    | Def Name [Exp s]
	    | Lam (Exp s) [Exp s]

type Exp s = Ptr s (ExpR s)

data Case s
	= Done (Exp s)
	| Skip (Case s)
	| Bind (Case s)
	| Split (NameMap (Case s))

type Name = Int
type NameMap = Map Name

type M = HeapM

appsR :: ExpR s -> [Exp s] -> ExpR s
appsR e		[]  = e
appsR (Var n es) es' = Var n $ es ++ es'
appsR (Con c es) es' = Con c $ es ++ es'
appsR (Def c es) es' = Def c $ es ++ es'
appsR (Lam e es) es' = Lam e $ es ++ es'

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
    compile e nmap = case appView e of
	Apps (S.Var n) es -> var n		  =<< comps es
	Apps (S.Con c) es -> con (nmap ! c)	  =<< comps es
	Apps (S.Def c) es -> def (nmap ! c)	  =<< comps es
	Apps (S.Lam v) es -> do
	    v' <- compile v nmap
	    vs <- comps es
	    lam v' vs
	where
	    comps es = mapM (flip compile nmap) es

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

		    isVar VarP	= True
		    isVar WildP = True
		    isVar _	= False

		    isCon (ConP _ _) = True
		    isCon _	     = False

		    conName (ConP c _ ) = c
		    conArgs (ConP c vs) = vs

decompile :: NameMap S.Name -> Exp s -> M s S.Exp
decompile nmap e = do
    e <- deref e
    case e of
	Var n es -> S.apps (S.Var n) <$> mapM dec es
	Con c es -> S.apps (S.Con (nmap ! c)) <$> mapM dec es
	Def c es -> S.apps (S.Def (nmap ! c)) <$> mapM dec es
	Lam e es -> do
	    e <- dec e
	    es <- mapM dec es
	    return $ S.Lam e `S.apps` es
    where
	dec = decompile nmap
	(!) = (Map.!)

-- Evaluation

data Condition = Broken | Pristine

instance Monoid Condition where
    mempty = Pristine
    mappend Broken _   = Broken
    mappend Pristine c = c

type RaiseM s = StateT Condition (M s)

needRepairs :: a -> (b -> RaiseM s a) -> RaiseM s b -> RaiseM s a
needRepairs original repair takeApart = do
    parts <- takeApart
    c	  <- get
    case c of
	Pristine -> return original
	Broken   -> repair parts

localRepairs :: RaiseM s a -> RaiseM s a
localRepairs m = do
    c <- get
    put Pristine
    x <- m
    modify (mappend c)
    return x

raiseFrom :: Int -> Int -> Exp s -> RaiseM s (Exp s)
raiseFrom n k e = localRepairs $ do
    v <- lift $ deref e
    case v of
	Var m es
	    | m < n	-> needRepairs e (lift . var m) $ mapM (raiseFrom n k) es
	    | otherwise -> do
		put Broken
		lift . var (m + k) =<< mapM (raiseFrom n k) es
	Con c es	-> needRepairs e (lift . con c) $ mapM (raiseFrom n k) es
	Def c es	-> needRepairs e (lift . def c) $ mapM (raiseFrom n k) es
	Lam b es	-> needRepairs e (lift . uncurry lam) $ do
	    b  <- raiseFrom (n + 1) k b
	    es <- mapM (raiseFrom n k) es
	    return (b, es)

raise :: Int -> Exp s -> M s (Exp s)
raise n e = evalStateT (raiseFrom 0 n e) Pristine

subst :: [Exp s] -> Exp s -> M s (Exp s)
subst us v = do
    v <- deref v
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
whnf ctx sig v = onThunk v $ \v -> case v of
    Var n vs	   -> return $ Var n vs
    Con c vs	   -> return $ Con c vs
    Def c vs	   -> iota ctx sig c vs
    Lam u (v : vs) -> do
	sub <- top ctx v
	whnf ctx sig =<< flip apps vs =<< subst sub u
    Lam u []	   -> return $ Lam u []

eval' :: Int -> Sig s -> Exp s -> M s ()
eval' ctx sig v = do
    whnf ctx sig v
    onThunk v $ \v -> case v of
	Lam u [] -> eval' (ctx + 1) sig u >> return v
	Var n vs -> mapM (eval' ctx sig) vs >> return v
	Con c vs -> mapM (eval' ctx sig) vs >> return v
	Def c vs -> mapM (eval' ctx sig) vs >> return v
    return ()

eval :: S.Sig -> S.Exp -> S.Exp
eval sig e = runHeap (do
	(sig', nmap, imap) <- compile sig
	v <- compile e imap
	eval' 0 sig' v
	decompile nmap v
    )
