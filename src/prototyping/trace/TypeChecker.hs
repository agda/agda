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

type Trace   = Current
type Sibling = Child

data Current = Current Call Parent [Sibling] [Child] | TopLevel [Child]
data Parent  = Parent  Call Parent [Sibling] | NoParent
data Child   = Child   Call [Child]

noTrace :: Trace
noTrace = TopLevel []

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

-- | Turn the tree the right way up (TopLevel at the root).
topLevelView :: Trace -> Trace
topLevelView t@(TopLevel _)	 = t
topLevelView t@(Current c _ _ _) = topLevelView $ updateCall c t

instance Show Current where
    show t = case topLevelView t of
	TopLevel cs -> unlines $ map show cs

instance Show Child where
    show (Child c cs) =
	indent 0 (show c) ++ indent 2 (unlines $ map show $ reverse cs)

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
newCall c (TopLevel cs)	       = Current c NoParent cs []
newCall c (Current c' p ss cs) = Current c (Parent c' p ss) cs []

updateCall :: Call -> Trace -> Trace
updateCall c (TopLevel _)	 = error $ "updateCall: no call in progress"
updateCall c (Current _ p ss cs) = case p of
    NoParent	     -> TopLevel $ Child c cs : ss
    Parent c' p' ss' -> Current c' p' ss' $ Child c cs : ss

call :: (Maybe r -> Call) -> TC r -> TC r
call mkCall m = do
    modify $ newCall (mkCall Nothing)
    r <- m
    modify $ updateCall (mkCall $ Just r)
    return r

-- Type errors ------------------------------------------------------------

data ErrorMsg = UnboundVar Ident
	      | TypeMismatch Type Type
	      | NotFunctionType Type
	      | InternalError String

instance Show ErrorMsg where
    show e = case e of
	UnboundVar x	  -> "Unbound variable " ++ printTree x
	TypeMismatch s t  -> printTree s ++ " != " ++ printTree t
	NotFunctionType t -> printTree t ++ " is not a function type"
	InternalError s   -> "Internal error: " ++ s

type TypeError = (Trace, ErrorMsg)

instance Error TypeError where
    noMsg    = (noTrace,InternalError "")
    strMsg s = (noTrace,InternalError s)

-- Typechecking monad -----------------------------------------------------

newtype TC a = TC { unTC :: ReaderT Context (StateT Trace (Either TypeError)) a }
    deriving (MonadReader Context, MonadState Trace)

instance Monad TC where
    return = TC . return
    TC m >>= k = TC $ m >>= unTC . k
    fail = failure . InternalError

failure :: ErrorMsg -> TC a
failure msg = do
    tr <- get
    TC $ lift $ lift $ Left (tr, msg)

runTC :: TC a -> Either TypeError a
runTC (TC tc) = evalStateT (runReaderT tc emptyContext) noTrace

-- The type checker -------------------------------------------------------

lookupVar :: Ident -> TC Type
lookupVar x = call (LookupVar x) $ do
    ctx <- ask
    case Map.lookup x ctx of
	Just t	-> return t
	Nothing	-> failure $ UnboundVar x

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
    _ -> failure $ TypeMismatch s t

isFunctionType :: Type -> TC (Type, Type)
isFunctionType t = call (IsFunctionType t) $ case t of
    FunT t1 t2	-> return (t1, t2)
    _		-> failure $ NotFunctionType t

-- Error message presentation ---------------------------------------------

matchCall :: (Call -> Maybe a) -> Trace -> Maybe a
matchCall f = matchTrace f'
    where
	f' (Child c _) = f c

matchTrace :: (Child -> Maybe a) -> Trace -> Maybe a
matchTrace f (TopLevel _) = Nothing
matchTrace f t@(Current c _ _ cs) =
    f (Child c cs) `mplus` matchTrace f (updateCall c t)

displayError :: TypeError -> String
displayError (tr, e) = case e of
    InternalError s	-> unlines [ "internal error: " ++ s ]
    UnboundVar x	-> unlines [ "unbound variable " ++ printTree x ]
    NotFunctionType t	->
	indent 0 $ unlines
		[ "the expression"
		, "  " ++ printTree f
		, "is applied to an argument, but has type"
		, "  " ++ printTree t
		, "which is not a function type"
		] -- show tr
	where
	    f = case matchCall isInferApp tr of
		    Just f  -> f
		    Nothing -> error "displayError: can't find function"
	    isInferApp (Infer (App f _) Nothing) = Just f
	    isInferApp _			 = Nothing

    TypeMismatch s t ->
	indent 0 $ unlines
	    [ "When checking the type of"
	    , "  " ++ printTree e
	    , "the inferred type"
	    , "  " ++ printTree t'
	    , "does not match the expected type"
	    , "  " ++ printTree s'
	    , "because"
	    , "  " ++ printTree s ++ " != " ++ printTree t
	    ]
	-- show tr
	where
	    isCheck (Child (Check e _ Nothing) (Child (EqualType s t _) _ : _)) = Just (e,s,t)
	    isCheck _ = Nothing

	    (e,s',t') = case matchTrace isCheck tr of
		Just (e,s,t) -> (e,s,t)
		Nothing	     -> error $ "displayError: weird type mismatch"
