
module TypeChecker where

import Syntax
--import PrintCore
--import Names
--import Substitution
--import Value

type TC a = Maybe a

-- | Invariant: For @[(xn,An),..,(x1,A1)]@ we have
--   @isType [(xi-1,Ai-1)..(x1,A1)] Ai@
type Context = [Type]

(#) :: Context -> Type -> Context
g # t = g ++ [t]

lookupType :: Context -> Int -> Type
lookupType g n = g !! n

isType :: Context -> Term -> TC Type
isType g t =
    case t of
	Set	    -> return SetT
	App El m    -> do check g m Set
			  return $ ElT m
	Fun `App` a `App` Lam x b ->
	    do	a' <- isType g a
		b' <- isType (g # (x,a)) b
		return $ FunT a' x b'
	_		-> fail $ "Not a type: " ++ printTree t

infer :: Context -> Term -> TC Type
infer g t =
    case t of
	Var x	-> lookupType g x
	App s t	->
	    do	(a, x, b) <- isFunctionType =<< infer g s
		check g t a
		return $ substitute b (x,t)
	_	-> fail $ "Can't infer the type of " ++ printTree t

check :: Context -> Term -> Type -> TC ()
check g (Lam x t) c =
    do	(a, y, b) <- isFunctionType c
	let (z, t', b') = matchBoundVar (Lam x t) (Lam y b)
	check (g # (z,a)) t' b'
check g t b =
    do	a <- infer g t
	convertType g a b

normalise :: Term -> Value
normalise t =
    case t of
	App s t	->
	    case normalise s of
		VLam x s  -> normalise $ substitute s (x,t)  
		VApp x vs -> VApp x $ vs ++ [normalise t]
	Var x	-> VApp x []
	Lam x t	-> VLam x t
	_	-> error $ "normalise: Not a well-formed term " ++ printTree t

-- | Precondition: both terms are lambdas. Returns the new bound variable
--   and the two renamed bodies.
matchBoundVar :: Term -> Term -> (Ident, Term, Term)
matchBoundVar (Lam x s) (Lam y t) = (z, rename s (x,z), rename t (y,z))
    where
	z = freshVar x (allVars $ App s t)
matchBoundVar s t =
    error $ "matchBoundVar: Violated precondition. " ++
	    printTree s ++ " and " ++ printTree t ++ " should be lambdas."

-- | Precondition: both terms are types in the given context.
convertType :: Context -> Type -> Type -> TC ()
convertType g Set Set = return ()
convertType g (App El s) (App El t) = convertTerm g s t Set
convertType g (Fun `App` a1 `App` Lam x b1)
	      (Fun `App` a2 `App` Lam y b2) =
    do	convertType g a1 a2
	let (z, b1', b2') = matchBoundVar (Lam x b1) (Lam y b2)
	convertType (g # (z,a1)) b1' b2'
convertType g a b =
    fail $ "Not convertible: " ++ printTree a ++ " and " ++ printTree b

-- | Precondition: the terms have the type in the context.
convertTerm :: Context -> Term -> Term -> Type -> TC ()

convertTerm g s t (Fun `App` a `App` Lam x b) =
	convertTerm (g # (z,a)) (s `App` Var z) (t `App` Var z) b'
    where
	z  = freshVar x (allVars $ s `App` t `App` b)
	b' = rename b (x,z)

convertTerm g s t a = undefined --normalise s === normalise t
    --where

isFunctionType :: Type -> TC (Type, Ident, Type)
isFunctionType (Fun `App` a `App` Lam x b) = return (a,x,b)
isFunctionType t = fail $ "Not a function type: " ++ printTree t

