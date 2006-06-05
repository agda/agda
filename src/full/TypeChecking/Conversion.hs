{-# OPTIONS -cpp -fglasgow-exts #-}

module TypeChecking.Conversion where

import Data.Generics

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.MetaVars
import TypeChecking.Substitute
import TypeChecking.Reduce
import TypeChecking.Constraints

import Utils.Monad

import TypeChecking.Monad.Debug

#include "../undefined.h"

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
	let tel = map (fmap $ const $ Sort Prop) args1 -- types don't matter here
        setRef Why x $ inst $ abstract tel (v `apply` newArgs)
    else fail $ "equalSameVar"
    where
	Arg _ (Var i []) === Arg _ (Var j []) = i == j
	_		 === _		      = False


-- | Type directed equality on values.
--
equalVal :: Data a => a -> Type -> Term -> Term -> TCM ()
equalVal _ a m n =
    catchConstraint (ValueEq a m n) $
    do	a' <- instantiate a
--     debug $ "equalVal " ++ show m ++ " == " ++ show n ++ " : " ++ show a'
	proofIrr <- proofIrrelevance
	s <- reduce =<< getSort a'
	case (proofIrr, s) of
	    (True, Prop)    -> return ()
	    _		    ->
		case a' of
		    Pi a _    -> equalFun (a,a') m n
		    Fun a _   -> equalFun (a,a') m n
		    MetaT x _ -> addConstraint (ValueEq a m n)
		    El _ _    -> equalAtm Why a m n
		    Sort _    -> equalAtm Why a m n
		    LamT _    -> __IMPOSSIBLE__
    where
	equalFun (a,t) m n =
	    {-# SCC "equalFun" #-}
	    do	name <- freshName_ (suggest t)
		addCtx name (unArg a) $ equalVal Why t' m' n'
	    where
		p	= fmap (const $ Var 0 []) a
		(m',n') = raise 1 (m,n) `apply` [p]
		t'	= raise 1 t `piApply` [p]
		suggest (Fun _ _) = "_"
		suggest (Pi _ (Abs x _)) = x
		suggest _ = __IMPOSSIBLE__

-- | Syntax directed equality on atomic values
--
equalAtm :: Data a => a -> Type -> Term -> Term -> TCM ()
equalAtm _ t m n =
    catchConstraint (ValueEq t m n) $
    do	(m, n) <- {-# SCC "equalAtm.reduce" #-} reduce (m, n)
	case (m, n) of
	    (Lit l1, Lit l2) | l1 == l2 -> return ()
	    (Var i iArgs, Var j jArgs) | i == j -> do
		a <- typeOfBV i
		equalArg Why a iArgs jArgs
	    (Def x xArgs, Def y yArgs) | x == y -> do
		a <- defType <$> getConstInfo x
		equalArg Why a xArgs yArgs
	    (Con x xArgs, Con y yArgs)
		| x == y -> do
		    a <- defType <$> getConstInfo x
		    equalArg Why a xArgs yArgs
	    (MetaV x xArgs, MetaV y yArgs) | x == y ->
		equalSameVar (\x -> MetaV x []) InstV x xArgs yArgs
	    (MetaV x xArgs, _) -> assignV t x xArgs n
	    (_, MetaV x xArgs) -> assignV t x xArgs m
	    (BlockedV b, _)    -> addConstraint (ValueEq t m n)
	    (_,BlockedV b)     -> addConstraint (ValueEq t m n)
	    _		       -> fail $ "equalAtm "++(show m)++" ==/== "++(show n)


-- | Type-directed equality on argument lists
--
equalArg :: Data a => a -> Type -> Args -> Args -> TCM ()
equalArg _ a args1 args2 = do
    a' <- instantiate a
    case (a', args1, args2) of 
        (_, [], []) -> return ()
        (Pi (Arg _ b) (Abs _ c), (Arg _ arg1 : args1), (Arg _ arg2 : args2)) -> do
            equalVal Why b arg1 arg2
            equalArg Why (subst arg1 c) args1 args2
        (Fun (Arg _ b) c, (Arg _ arg1 : args1), (Arg _ arg2 : args2)) -> do
            equalVal Why b arg1 arg2
            equalArg Why c args1 args2
        _ -> fail $ "equalArg "++(show a)++" "++(show args1)++" "++(show args2)


-- | Equality on Types
equalTyp :: Data a => a -> Type -> Type -> TCM ()
equalTyp _ a1 a2 =
    catchConstraint (TypeEq a1 a2) $
    do	do  s1 <- getSort a1
	    s2 <- getSort a2
	    equalSort s1 s2
	a1' <- instantiate a1
	a2' <- instantiate a2
	ctx <- map fst <$> getContext
-- 	debug $ "equalTyp in " ++ show ctx
-- 	debug $ "            " ++ show a1 ++ " == " ++ show a2
-- 	debug $ "            " ++ show a1' ++ " == " ++ show a2'
	case (a1', a2') of
	    _ | f1@(FunV _ _) <- funView a1'
	      , f2@(FunV _ _) <- funView a2' -> equalFun f1 f2
	    (El m1 s1, El m2 s2) ->
		equalVal Why (sort s1) m1 m2
	    (Sort s1, Sort s2) -> equalSort s1 s2
	    (MetaT x xDeps, MetaT y yDeps) | x == y -> 
		equalSameVar (\x -> MetaT x []) InstT x xDeps yDeps
	    (MetaT x xDeps, a) -> assignT x xDeps a 
	    (a, MetaT x xDeps) -> assignT x xDeps a 
	    (LamT _, _)  -> __IMPOSSIBLE__
	    (El _ _, _)  -> fail $ show a1' ++ " != " ++ show a2'
	    (Pi _ _, _)  -> fail $ show a1' ++ " != " ++ show a2'
	    (Fun _ _, _) -> fail $ show a1' ++ " != " ++ show a2'
	    (Sort _, _)  -> fail $ show a1' ++ " != " ++ show a2'

    where
	equalFun (FunV (Arg h1 a1) t1) (FunV (Arg h2 a2) t2)
	    | h1 /= h2	= fail $ show a1 ++ " != " ++ show a2
	    | otherwise =
		do  equalTyp Why a1 a2
		    let (t1',t2') = raise 1 (t1,t2)
			arg	  = Arg h1 (Var 0 [])
		    name <- freshName_ (suggest t1 t2)
		    addCtx name a1 $ equalTyp Why (piApply t1' [arg]) (piApply t2' [arg])
	    where
		suggest t1 t2 = case concatMap name [t1,t2] of
				    []	-> "_"
				    x:_	-> x
		    where
			name (Pi _ (Abs x _)) = [x]
			name (Fun _ _)	      = []
			name _		      = __IMPOSSIBLE__
	equalFun _ _ = __IMPOSSIBLE__


---------------------------------------------------------------------------
-- * Sorts
---------------------------------------------------------------------------

-- | Check that the first sort is less or equal to the second.
leqSort :: Sort -> Sort -> TCM ()
leqSort s1 s2 =
    catchConstraint (SortLeq s1 s2) $
    do	(s1,s2) <- reduce (s1,s2)
-- 	debug $ "leqSort " ++ show s1 ++ " <= " ++ show s2
	case (s1,s2) of

	    (Prop    , Prop    )	     -> return ()
	    (Type _  , Prop    )	     -> notLeq s1 s2
	    (Suc _   , Prop    )	     -> notLeq s1 s2

	    (Prop    , Type _  )	     -> return ()
	    (Type n  , Type m  ) | n <= m    -> return ()
				 | otherwise -> notLeq s1 s2
	    (Suc s   , Type n  ) | 1 <= n    -> leqSort s (Type $ n - 1)
				 | otherwise -> notLeq s1 s2
	    (_	     , Suc _   )	     -> addConstraint (SortLeq s1 s2)

	    (Lub a b , _       )	     -> leqSort a s2 >> leqSort b s2
	    (_	     , Lub _ _ )	     -> addConstraint (SortLeq s1 s2)

	    (MetaS x , MetaS y ) | x == y    -> return ()
	    (MetaS x , _       )	     -> addConstraint (SortLeq s1 s2)
	    (_	     , MetaS x )	     -> addConstraint (SortLeq s1 s2)
    where
	notLeq s1 s2 = fail $ show s1 ++ " is not less or equal to " ++ show s2

-- | Check that the first sort equal to the second.
equalSort :: Sort -> Sort -> TCM ()
equalSort s1 s2 =
    catchConstraint (SortEq s1 s2) $
    do	(s1,s2) <- reduce (s1,s2)
-- 	debug $ "equalSort " ++ show s1 ++ " == " ++ show s2
	case (s1,s2) of

	    (Prop    , Prop    )	     -> return ()
	    (Type _  , Prop    )	     -> notEq s1 s2
	    (Prop    , Type _  )	     -> notEq s1 s2

	    (Type n  , Type m  ) | n == m    -> return ()
				 | otherwise -> notEq s1 s2
	    (Suc s   , Prop    )	     -> notEq s1 s2
	    (Suc s   , Type 0  )	     -> notEq s1 s2
	    (Suc s   , Type 1  )	     -> addConstraint (SortEq s1 s2)
	    (Suc s   , Type n  )	     -> equalSort s (Type $ n - 1)
	    (Prop    , Suc s   )	     -> notEq s1 s2
	    (Type 0  , Suc s   )	     -> notEq s1 s2
	    (Type 1  , Suc s   )	     -> addConstraint (SortEq s1 s2)
	    (Type n  , Suc s   )	     -> equalSort (Type $ n - 1) s
	    (_	     , Suc _   )	     -> addConstraint (SortEq s1 s2)
	    (Suc _   , _       )	     -> addConstraint (SortEq s1 s2)

	    (Lub _ _ , _       )	     -> addConstraint (SortEq s1 s2)
	    (_	     , Lub _ _ )	     -> addConstraint (SortEq s1 s2)

	    (MetaS x , MetaS y ) | x == y    -> return ()
				 | otherwise -> assignS x s2
	    (MetaS x , Type _  )	     -> assignS x s2
	    (MetaS x , Prop    )	     -> assignS x s2
	    (_	     , MetaS x )	     -> equalSort s2 s1
    where
	notEq s1 s2 = fail $ show s1 ++ " is not equal to " ++ show s2

-- | Get the sort of a type. Should be moved somewhere else.
getSort :: Type -> TCM Sort
getSort t =
    case t of
	El _ s		       -> return s
	Pi (Arg _ a) (Abs _ b) -> sLub <$> getSort a <*> getSort b
	Fun (Arg _ a) b	       -> sLub <$> getSort a <*> getSort b
	Sort s		       -> return $ sSuc s
	MetaT m _	       ->
	    do  mv <- mvJudgement <$> lookupMeta m
		case mv of
		    IsType _ s -> return s
		    _	       -> __IMPOSSIBLE__
	LamT _ -> __IMPOSSIBLE__

