{-# OPTIONS -fglasgow-exts #-}
module TypeChecker where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Error

import qualified Data.Map as Map
import Data.Maybe

import Lambda.Abs
import Lambda.Print

-- Context ----------------------------------------------------------------

type Context   = Map.Map Ident Type

emptyContext :: Context
emptyContext = Map.empty

-- Trace ------------------------------------------------------------------

newtype Trace = Trace [CallTree]

data CallTree = CallTree Call Trace

noTrace :: Trace
noTrace = Trace []

data Call = Infer Exp		(Maybe Type)
	  | Check Exp Type	(Maybe ())
	  | LookupVar Ident	(Maybe Type)
	  | EqualType Type Type (Maybe ())
	  | IsFunctionType Type (Maybe (Type,Type))

indent :: Int -> String -> String
indent _ "" = ""
indent n s  = unlines . concatMap ind . lines $ s
    where
	ind "" = []
	ind s = [replicate n ' ' ++ s]

instance Show Trace where
    show (Trace cs) = unlines $ map show $ reverse cs

instance Show CallTree where
    show (CallTree c t) = indent 0 (show c) ++ indent 2 (show t)

instance Show Call where
    show e = case e of
	Infer e r	   -> "infer " ++ show' e ++ " = " ++ res r
	Check e t r	   -> "check " ++ show' e ++ " " ++ show' t ++ " " ++ nores r
	LookupVar x r	   -> "lookupVar " ++ printTree x ++ " = " ++ res r
	EqualType s t r    -> show' s ++ " == " ++ show' t ++ " " ++ nores r
	IsFunctionType t r -> "isFunctionType " ++ show' t ++ " " ++ nores r
	where
	    show' x = par $ printTree x
	    par s
		| ' ' `elem` s = "(" ++ s ++ ")"
		| otherwise    = s
	    res Nothing = "?"
	    res (Just r) = printTree r
	    nores Nothing = "?"
	    nores (Just _) = ""

inProgress :: Call -> Bool
inProgress c = case c of
    Infer _ r	       -> isNothing r
    Check _ _ r	       -> isNothing r
    LookupVar _ r      -> isNothing r
    EqualType _ _ r    -> isNothing r
    IsFunctionType _ r -> isNothing r

newCall :: Call -> Trace -> Trace
newCall c (Trace cs) = Trace $ case cs of
    []	-> [call]
    CallTree c' t : cs'
	| inProgress c'	-> CallTree c' (newCall c t) : cs'
	| otherwise	-> call : cs
    where
	call = CallTree c $ Trace []

updateCall :: Call -> Trace -> Trace
updateCall c (Trace cs) = Trace $ case cs of
    []	-> error $ "updateCall: can't update an empty trace"
    CallTree c' t : cs'
	| inProgress c' -> case t of
	    Trace (CallTree c'' _ : _)
		| inProgress c'' -> CallTree c' (updateCall c t) : cs'
	    _			 -> CallTree c t : cs'
	| otherwise	-> error $ "updateCall: no call in progress"

call :: (Maybe r -> Call) -> TC r -> TC r
call mkCall m = do
    modify $ newCall (mkCall Nothing)
    r <- m
    modify $ updateCall (mkCall $ Just r)
    return r

-- Type errors ------------------------------------------------------------

type TypeError = (Trace, String)

instance Error TypeError where
    noMsg    = (noTrace,"")
    strMsg s = (noTrace,s)

-- Typechecking monad -----------------------------------------------------

newtype TC a = TC { unTC :: ReaderT Context (StateT Trace (Either TypeError)) a }
    deriving (MonadReader Context, MonadState Trace)

instance Monad TC where
    return = TC . return
    TC m >>= k = TC $ m >>= unTC . k
    fail s = do
	tr <- get
	TC $ lift $ lift $ Left (tr,s)

runTC :: TC a -> Either TypeError a
runTC (TC tc) = evalStateT (runReaderT tc emptyContext) noTrace

-- The type checker -------------------------------------------------------

lookupVar :: Ident -> TC Type
lookupVar x = call (LookupVar x) $ do
    ctx <- ask
    case Map.lookup x ctx of
	Just t	-> return t
	Nothing	-> fail $ "unbound variable " ++ show x

addToContext :: Ident -> Type -> TC a -> TC a
addToContext x t = local $ Map.insert x t

infer :: Exp -> TC Type
infer e = call (Infer e) $ case e of
    Var x     -> lookupVar x
    Lit _     -> return $ ConT (Ident "Nat")
    App e1 e2 -> do
	t	 <- infer e1
	(t1, t2) <- isFunctionType t
	check e2 t1
	return t2
    Lam x t e -> do
	t' <- addToContext x t $ infer e
	return $ FunT t t'

check :: Exp -> Type -> TC ()
check e t = call (Check e t) $ do
    t' <- infer e
    t === t'

(===) :: Type -> Type -> TC ()
s === t = call (EqualType s t) $ case (s,t) of
    (ConT x, ConT y)
	| x == y     -> return ()
    (FunT s1 t1, FunT s2 t2) -> do
	s1 === s2
	t1 === t2
    _ -> fail $ "type mismatch " ++ printTree s ++ " != " ++ printTree t

isFunctionType :: Type -> TC (Type, Type)
isFunctionType t = call (IsFunctionType t) $ case t of
    FunT t1 t2	-> return (t1, t2)
    _		-> fail $ "expected function type: " ++ printTree t

