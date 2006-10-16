{-# OPTIONS -cpp -fglasgow-exts #-}

module TypeChecking.Conversion where

import Control.Monad
import Data.Generics

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.MetaVars
import TypeChecking.Substitute
import TypeChecking.Reduce
import TypeChecking.Constraints
import TypeChecking.Errors

import Utils.Monad

import TypeChecking.Monad.Debug

#include "../undefined.h"

{-
-- | Equality of two instances of the same metavar
--
equalSameVar :: (Data a, Abstract a, Apply a) => 
                (MetaId -> a) -> (a -> MetaInstantiation) -> MetaId -> Args -> Args -> TCM ()
equalSameVar meta inst x args1 args2 =
    if length args1 == length args2 then do
        -- next 2 checks could probably be nicely merged into construction 
        --   of newArgs using ListT, but then can't use list comprehension.
        checkArgs x args1 
        checkArgs x args2 
        let idx = [0 .. length args1 - 1]
        let newArgs = [ Arg NotHidden $ Var n []
		      | (n, (a,b)) <- zip idx $ reverse $ zip args1 args2
		      , a === b
		      ]
        v <- newMetaSame x meta
	let tel = map (fmap $ const ("_", sort Prop)) args1
		-- only hiding matters
        setRef x $ inst $ abstract tel (v `apply` newArgs)
    else fail $ "equalSameVar"
    where
	Arg _ (Var i []) === Arg _ (Var j []) = i == j
	_		 === _		      = False
-}

-- | Type directed equality on values.
--
equalVal :: Type -> Term -> Term -> TCM Constraints
equalVal a m n =
    catchConstraint (ValueEq a m n) $
    do	a' <- instantiate a
--     debug $ "equalVal " ++ show m ++ " == " ++ show n ++ " : " ++ show a'
	proofIrr <- proofIrrelevance
	s <- reduce $ getSort a'
	case (proofIrr, s) of
	    (True, Prop)    -> return []
	    _		    ->
		case unEl a' of
		    Pi a _    -> equalFun (a,a') m n
		    Fun a _   -> equalFun (a,a') m n
		    MetaV x _ -> buildConstraint (ValueEq a m n)
		    Lam _ _   -> __IMPOSSIBLE__
		    _	      -> equalAtm a' m n
    where
	equalFun (a,t) m n =
	    do	name <- freshName_ (suggest $ unEl t)
		addCtx name (unArg a) $ equalVal t' m' n'
	    where
		p	= fmap (const $ Var 0 []) a
		(m',n') = raise 1 (m,n) `apply` [p]
		t'	= raise 1 t `piApply'` [p]
		suggest (Fun _ _) = "_"
		suggest (Pi _ (Abs x _)) = x
		suggest _ = __IMPOSSIBLE__

-- | Syntax directed equality on atomic values
--
equalAtm :: Type -> Term -> Term -> TCM Constraints
equalAtm t m n =
    catchConstraint (ValueEq t m n) $
    do	(m, n) <- {-# SCC "equalAtm.reduce" #-} reduce (m, n)
	case (m, n) of
	    _ | f1@(FunV _ _) <- funView m
	      , f2@(FunV _ _) <- funView n -> equalFun f1 f2

	    (Sort s1, Sort s2) -> equalSort s1 s2

	    (Lit l1, Lit l2) | l1 == l2 -> return []
	    (Var i iArgs, Var j jArgs) | i == j -> do
		a <- typeOfBV i
		equalArg a iArgs jArgs
	    (Def x xArgs, Def y yArgs) | x == y -> do
		a <- defType <$> getConstInfo x
		equalArg a xArgs yArgs
	    (Con x xArgs, Con y yArgs)
		| x == y -> do
		    a <- defType <$> getConstInfo x
		    equalArg a xArgs yArgs
	    (MetaV x xArgs, MetaV y yArgs) | x == y ->
		buildConstraint (ValueEq t m n)
		-- equalSameVar (\x -> MetaV x []) InstV x xArgs yArgs
	    (MetaV x xArgs, _) -> assignV t x xArgs n
	    (_, MetaV x xArgs) -> assignV t x xArgs m
	    (BlockedV b, _)    -> buildConstraint (ValueEq t m n)
	    (_,BlockedV b)     -> buildConstraint (ValueEq t m n)
	    _		       -> typeError $ UnequalTerms m n t
    where
	equalFun (FunV (Arg h1 a1) t1) (FunV (Arg h2 a2) t2)
	    | h1 /= h2	= typeError $ UnequalHiding ty1 ty2
	    | otherwise =
		do  cs  <- equalTyp a1 a2
		    let (ty1',ty2') = raise 1 (ty1,ty2)
			arg	  = Arg h1 (Var 0 [])
		    name <- freshName_ (suggest t1 t2)
		    cs' <- addCtx name a1 $ equalTyp (piApply' ty1' [arg]) (piApply' ty2' [arg])
		    return $ cs ++ cs'
	    where
		ty1 = El (getSort a1) t1    -- TODO: wrong (but it doesn't matter)
		ty2 = El (getSort a2) t2
		suggest t1 t2 = case concatMap name [t1,t2] of
				    []	-> "_"
				    x:_	-> x
		    where
			name (Pi _ (Abs x _)) = [x]
			name (Fun _ _)	      = []
			name _		      = __IMPOSSIBLE__
	equalFun _ _ = __IMPOSSIBLE__



-- | Type-directed equality on argument lists
--
equalArg :: Type -> Args -> Args -> TCM Constraints
equalArg a args1 args2 = do
    a' <- reduce a
    case (unEl a', args1, args2) of 
        (_, [], []) -> return []
        (Pi (Arg _ b) (Abs _ c), (Arg _ arg1 : args1), (Arg _ arg2 : args2)) -> do
            cs  <- equalVal b arg1 arg2
            cs' <- equalArg (subst arg1 c) args1 args2
	    return $ cs ++ cs'
        (Fun (Arg _ b) c, (Arg _ arg1 : args1), (Arg _ arg2 : args2)) -> do
            cs  <- equalVal b arg1 arg2
            cs' <- equalArg c args1 args2
	    return $ cs ++ cs'
        _ -> __IMPOSSIBLE__


-- | Equality on Types
equalTyp :: Type -> Type -> TCM Constraints
equalTyp ty1@(El s1 a1) ty2@(El s2 a2) =
    catchConstraint (TypeEq ty1 ty2) $ do
	cs1 <- equalSort s1 s2
	cs2 <- equalVal (sort s1) a1 a2
	return $ cs1 ++ cs2

leqType :: Type -> Type -> TCM Constraints
leqType ty1@(El s1 a1) ty2@(El s2 a2) = do
     -- TODO: catchConstraint (?)
    (a1, a2) <- reduce (a1,a2)
    case (a1, a2) of
	(Sort s1, Sort s2) -> leqSort s1 s2
	_		   -> equalTyp (El s1 a1) (El s2 a2)
	    -- TODO: subtyping for function types

---------------------------------------------------------------------------
-- * Sorts
---------------------------------------------------------------------------

-- | Check that the first sort is less or equal to the second.
leqSort :: Sort -> Sort -> TCM Constraints
leqSort s1 s2 =
    catchConstraint (SortEq s1 s2) $
    do	(s1,s2) <- reduce (s1,s2)
-- 	do  d1 <- prettyTCM s1
-- 	    d2 <- prettyTCM s2
-- 	    debug $ "leqSort   " ++ show d1 ++ " <= " ++ show d2
	case (s1,s2) of

	    (Prop    , Prop    )	     -> return []
	    (Type _  , Prop    )	     -> notLeq s1 s2
	    (Suc _   , Prop    )	     -> notLeq s1 s2

	    (Prop    , Type _  )	     -> return []
	    (Type n  , Type m  ) | n <= m    -> return []
				 | otherwise -> notLeq s1 s2
	    (Suc s   , Type n  ) | 1 <= n    -> leqSort s (Type $ n - 1)
				 | otherwise -> notLeq s1 s2
	    (_	     , Suc _   )	     -> equalSort s1 s2

	    (Lub a b , _       )	     -> liftM2 (++) (leqSort a s2) (leqSort b s2)
	    (_	     , Lub _ _ )	     -> equalSort s1 s2

	    (MetaS x , MetaS y ) | x == y    -> return []
	    (MetaS x , _       )	     -> equalSort s1 s2
	    (_	     , MetaS x )	     -> equalSort s1 s2
    where
	notLeq s1 s2 = typeError $ NotLeqSort s1 s2

-- | Check that the first sort equal to the second.
equalSort :: Sort -> Sort -> TCM Constraints
equalSort s1 s2 =
    catchConstraint (SortEq s1 s2) $
    do	(s1,s2) <- reduce (s1,s2)
-- 	do  d1 <- prettyTCM s1
-- 	    d2 <- prettyTCM s2
-- 	    debug $ "equalSort " ++ show d1 ++ " == " ++ show d2
	case (s1,s2) of

	    (Prop    , Prop    )	     -> return []
	    (Type _  , Prop    )	     -> notEq s1 s2
	    (Prop    , Type _  )	     -> notEq s1 s2

	    (Type n  , Type m  ) | n == m    -> return []
				 | otherwise -> notEq s1 s2
	    (Suc s   , Prop    )	     -> notEq s1 s2
	    (Suc s   , Type 0  )	     -> notEq s1 s2
	    (Suc s   , Type 1  )	     -> buildConstraint (SortEq s1 s2)
	    (Suc s   , Type n  )	     -> equalSort s (Type $ n - 1)
	    (Prop    , Suc s   )	     -> notEq s1 s2
	    (Type 0  , Suc s   )	     -> notEq s1 s2
	    (Type 1  , Suc s   )	     -> buildConstraint (SortEq s1 s2)
	    (Type n  , Suc s   )	     -> equalSort (Type $ n - 1) s
	    (_	     , Suc _   )	     -> buildConstraint (SortEq s1 s2)
	    (Suc _   , _       )	     -> buildConstraint (SortEq s1 s2)

	    (Lub _ _ , _       )	     -> buildConstraint (SortEq s1 s2)
	    (_	     , Lub _ _ )	     -> buildConstraint (SortEq s1 s2)

	    (MetaS x , MetaS y ) | x == y    -> return []
				 | otherwise -> assignS x s2
	    (MetaS x , Type _  )	     -> assignS x s2
	    (MetaS x , Prop    )	     -> assignS x s2
	    (_	     , MetaS x )	     -> equalSort s2 s1
    where
	notEq s1 s2 = typeError $ UnequalSorts s1 s2
-- 	buildConstraint c@(SortEq s1 s2) = do
-- 	    d1 <- prettyTCM s1
-- 	    d2 <- prettyTCM s2
-- 	    debug $ "Can't solve " ++ show d1 ++ " == " ++ show d2
-- 	    TypeChecking.Monad.buildConstraint c
-- 	buildConstraint _ = __IMPOSSIBLE__

