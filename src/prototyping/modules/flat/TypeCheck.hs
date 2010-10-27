{-# OPTIONS_GHC -fglasgow-exts #-}

module TypeCheck where

import Prelude hiding (mapM)
import Control.Applicative
import Control.Monad.State hiding (mapM)
import Control.Monad.Reader hiding (mapM)
import Control.Monad.Error hiding (mapM)
import Data.Map (Map)
import Data.List
import Data.Traversable
import qualified Data.Map as Map
import Text.PrettyPrint

import Abstract (Var, Name)
import qualified Abstract as A
import qualified Scope as A
import Internal
import Pretty
import Debug
import Utils

data TCState = TCState
	{ sections  :: Map A.ModuleName Tel
	, functions :: Map Name Defn
	}

instance Show TCState where show = show . pretty

instance Pretty TCState where
    pretty tc = vcat $
	map showSection (Map.toList $ sections tc) ++
	map showFun (Map.toList $ functions tc)
	where
	    showSection (x,tel) =
		sep [ text "section" <+> A.prettyName x
		    , nest 2 $ fsep $ showTel [] tel
		    ]
	    showTel ctx [] = []
	    showTel ctx ((x,t):tel) =
		parens (
		    text x' <+> text ":" <+> pretty (toExpr ctx t)
		) : showTel (x' : ctx) tel
		where
		    x' = fresh ctx x
	    showFun (x, Type _ _ a)    = pretty $ A.Type x (toExpr [] a)
	    showFun (x, Value _ _ a t) = pretty $ A.Defn x [] (toExpr [] a) (toExpr [] t) []


-- Telescopes are reversed contexts
type Tel = [(Var, Type)]
type Context = [(Var, Type)]

type TCM = ReaderT Context (StateT TCState (Either String))

runTCM :: TCM a -> Either String TCState
runTCM m = flip execStateT (TCState Map.empty Map.empty)
	 $ flip runReaderT []
	 $ m

class Abstract a where
    abstract :: Tel -> a -> a

instance Abstract Defn where
    abstract tel (Type x fv a)	  = Type  x (fv + length tel) $ abstract tel a
    abstract tel (Value x fv a t) = Value x (fv + length tel) (abstract tel a) (abstract tel t)

instance Abstract Type where
    abstract tel a = foldr (\(x,a) b -> Pi a (Abs x b)) a tel

instance Abstract Term where
    abstract tel t = foldr (\(x,_) t -> Lam (Abs x t)) t tel

instance Abstract Tel where
    abstract = (++)

class Raise a where
    raiseFrom :: Int -> Int -> a -> a

instance Raise Term where
    raiseFrom n k t = case t of
	Lam t	-> Lam $ raiseFrom n k t
	App s t -> (App `on` raiseFrom n k) s t
	Def c	-> Def c
	Var m
	    | m < n	-> Var m
	    | otherwise	-> Var (m + k)

instance Raise a => Raise (Abs a) where
    raiseFrom n k (Abs x b) = Abs x $ raiseFrom (n + 1) k b

raise :: Raise a => Int -> a -> a
raise = raiseFrom 0

class Subst a where
    substUnder :: Int -> Term -> a -> a

instance Subst Type where
    substUnder n t a = case a of
	Set -> Set
	Pi a b -> Pi (substUnder n t a) (substUnder n t b)
	El s -> El (substUnder n t s)

instance Subst Tel where
    substUnder _ _ [] = []
    substUnder n t ((x,a):as) = (x,substUnder n t a) : unAbs (substUnder n t $ Abs "_" as)

instance Subst Term where
    substUnder n s t = case t of
	Lam t	-> Lam (substUnder n s t)
	App t u -> (App `on` substUnder n s) t u
	Def c	-> Def c
	Var m
	    | m < n	-> Var m
	    | m > n	-> Var (m - 1)
	    | otherwise -> s

instance Subst a => Subst (Abs a) where
    substUnder n t (Abs x b) = Abs x $ substUnder (n + 1) (raise 1 t) b

subst :: Subst a => Term -> a -> a
subst = substUnder 0

class Apply a where
    apply :: [Term] -> a -> a

instance Apply Defn where
    apply ts (Type x fv a)    = Type  x (fv - length ts) $ apply ts a
    apply ts (Value x fv a t) = Value x (fv - length ts) (apply ts a) (apply ts t)

instance Apply Tel where
    apply []	 tel	= tel
    apply (t:ts) (_:as) = subst t $ apply ts as
    apply _ _ = error $ "bad telescope application"

instance Apply Type where
    apply [] a = a
    apply (t:ts) (Pi _ (Abs _ b)) = apply ts (subst t b)
    apply _ _ = error $ "bad type application"

instance Apply Term where
    apply [] t			 = t
    apply (t:ts) (Lam (Abs _ b)) = apply ts (subst t b)
    apply ts t			 = foldl App t ts

getContextTerms :: TCM [Term]
getContextTerms = do
    ctx <- getContext
    return $ reverse $ zipWith (const . Var) [0..] ctx

instantiate :: A.ModuleName -> A.ModuleName -> Tel -> [Term] -> TCM ()
instantiate new old tel ts = do
    s <- get
    let ss = Map.toList $ Map.filterWithKey (const . isPrefixOf old) $ sections s
	ds = Map.toList $ Map.filterWithKey (const . isPrefixOf old) $ functions s
    ts0 <- take (length tel - length ts) <$> getContextTerms
    mapM_ (copyDef $ ts0 ++ ts) ds
    mapM_ (copySec $ ts0 ++ ts) ss
    where
	copyName x = new ++ drop (length old) x
	copyDef :: [Term] -> (Name, Defn) -> TCM ()
	copyDef ts (x, d) = addDef (copyName x) d'
	    where
		d' = Value (copyName x) 0
			   (apply ts $ defType d)
			   (apply ts (Def x))

	copySec :: [Term] -> (Name, Tel) -> TCM ()
	copySec ts (x, tel) = addSection (copyName x) (apply ts tel)

addDef :: Name -> Defn -> TCM ()
addDef x d = do
    ctx <- getContextTel
    let d' = abstract ctx d
    modify $ \s -> s { functions = Map.insert x d' $ functions s }

addSection :: Name -> Tel -> TCM ()
addSection x [] = return ()
addSection x tel = do
    ctx <- getContextTel
    let tel' = abstract ctx tel
    modify $ \s -> s { sections = Map.insert x tel' $ sections s }

extendContext :: Var -> Type -> TCM a -> TCM a
extendContext x t = local $ (:) (x,t)

getContext :: TCM Context
getContext = ask

getContextTel :: TCM Tel
getContextTel = reverse <$> getContext

lookupVar :: Var -> TCM Int
lookupVar x = do
    ctx <- ask
    case findIndex ((x==) . fst) ctx of
	Just n	-> return n
	Nothing	-> fail $ "panic: no such variable " ++ x

lookupSection :: Name -> TCM Tel
lookupSection s = do
    ss <- gets sections
    case Map.lookup s ss of
	Just tel -> return tel
	Nothing	 -> return []

lookupDef :: Name -> TCM Defn
lookupDef c = do
  ds <- gets functions
  case Map.lookup c ds of
    Just d  -> return d
    Nothing -> fail $ "panic: no such name " ++ A.showName c

checkDecl :: A.Decl -> TCM ()
checkDecl d = case d of
    A.Type x e -> do
	t <- isType e
	addDef x (Type x 0 t)
    A.Defn x tel t e whr ->
      checkTel tel $ \_ -> do
	a <- isType t
	mapM_ checkDecl whr
	t <- checkType e
	addDef x (Value x 0 a t)
    A.Section x tel ds ->
	checkTel tel $ \_ -> do
	    addSection x [] -- tel is already in the context
	    mapM_ checkDecl ds
    A.Inst m1 m2 es -> do
	tel <- lookupSection m2
	ts <- mapM checkType es
	instantiate m1 m2 tel ts

checkTel :: A.Tel -> (Tel -> TCM a) -> TCM a
checkTel [] ret = ret []
checkTel ((x,e):tel) ret = do
    a <- isType e
    extendContext x a $ checkTel tel $ \tel -> ret ((x,a) : tel)

isType :: A.Expr -> TCM Type
isType e = case e of
    A.Set   -> return Set
    A.Pi x e1 e2 -> do
	a <- isType e1
	b <- extendContext x a $ isType e2
	return $ Pi a (Abs x b)
    e -> El <$> checkType e

checkType :: A.Expr -> TCM Term
checkType e = case e of
    A.Var x	-> Var <$> lookupVar x
    A.Def c	-> do
      def <- lookupDef c
      ts  <- getContextTerms
      return $ apply (take (defFreeVars def) ts) (Def c)
    A.App e1 e2 -> App <$> checkType e1 <*> checkType e2
    A.Lam x e	-> Lam . Abs x <$> extendContext x Set (checkType e)
    _		-> fail $ "not a term: " ++ show e
