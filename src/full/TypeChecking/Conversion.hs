{-# OPTIONS -cpp -fglasgow-exts #-}

module TypeChecking.Conversion where

import Control.Applicative
import Control.Monad
import Control.Monad.State
import Data.Generics

import Syntax.Common
import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.MetaVars
import TypeChecking.Substitute
import TypeChecking.Reduce
import TypeChecking.Constraints
import TypeChecking.Errors
import TypeChecking.Primitive (constructorForm)
import TypeChecking.Free
import TypeChecking.Records
import TypeChecking.Pretty
import TypeChecking.Injectivity

import Utils.Monad

import TypeChecking.Monad.Debug

#include "../undefined.h"

-- | Check if to lists of arguments are the same (and all variables).
--   Precondition: the lists have the same length.
sameVars :: Args -> Args -> Bool
sameVars xs ys = and $ zipWith same xs ys
    where
	same (Arg _ (Var n [])) (Arg _ (Var m [])) = n == m
	same _ _				   = False

-- | Type directed equality on values.
--
equalTerm :: MonadTCM tcm => Type -> Term -> Term -> tcm Constraints
equalTerm a m n =
    catchConstraint (ValueEq a m n) $
    do	a'	 <- reduce a
	proofIrr <- proofIrrelevance
	s	 <- reduce $ getSort a'
	case (proofIrr, s) of
	    (True, Prop)    -> return []
	    _		    ->
		case unEl a' of
		    Pi a _    -> equalFun (a,a') m n
		    Fun a _   -> equalFun (a,a') m n
		    MetaV x _ -> do
			(m,n) <- normalise (m,n)
			if m == n
			    then return []
			    else buildConstraint (ValueEq a m n)
		    Lam _ _   -> __IMPOSSIBLE__
		    Def r ps  -> do
		      isrec <- isRecord r
		      if isrec
			then do
			  (m, n) <- reduce (m, n)
			  case (m, n) of
			    _ | isNeutral m && isNeutral n ->
				equalAtom a' m n
			    _ -> do
			      (tel, m') <- etaExpandRecord r ps m
			      (_  , n') <- etaExpandRecord r ps n
			      equalArg (telePi_ tel $ sort Prop) m' n'
			else equalAtom a' m n
		    _	      -> equalAtom a' m n
    where
	isNeutral (MetaV _ _)  = False
	isNeutral (Con _ _)    = False
	isNeutral (BlockedV _) = False
	isNeutral _	       = True

	equalFun (a,t) m n =
	    do	name <- freshName_ (suggest $ unEl t)
		addCtx name a $ equalTerm t' m' n'
	    where
		p	= fmap (const $ Var 0 []) a
		(m',n') = raise 1 (m,n) `apply` [p]
		t'	= raise 1 t `piApply` [p]
		suggest (Fun _ _)	 = "x"
		suggest (Pi _ (Abs x _)) = x
		suggest _		 = __IMPOSSIBLE__

-- | Syntax directed equality on atomic values
--
equalAtom :: MonadTCM tcm => Type -> Term -> Term -> tcm Constraints
equalAtom t m n =
    catchConstraint (ValueEq t m n) $
    do	m <- constructorForm =<< reduce m
	n <- constructorForm =<< reduce n
	reportSDoc "tc.conv.atom" 10 $ fsep
	  [ text "equalAtom", prettyTCM m, text "==", prettyTCM n, text ":", prettyTCM t ]
	case (m, n) of
	    _ | f1@(FunV _ _) <- funView m
	      , f2@(FunV _ _) <- funView n -> equalFun f1 f2

	    (Sort s1, Sort s2) -> equalSort s1 s2

	    (Lit l1, Lit l2) | l1 == l2 -> return []
	    (Var i iArgs, Var j jArgs) | i == j -> do
		a <- typeOfBV i
		equalArg a iArgs jArgs
	    (Def x xArgs, Def y yArgs) | x == y -> do
		reportSDoc "tc.conv.atom" 20 $
		  text "equalArg" <+> sep [ brackets (fsep $ punctuate comma $ map prettyTCM xArgs)
					  , brackets (fsep $ punctuate comma $ map prettyTCM yArgs)
					  ]
		a <- defType <$> getConstInfo x
		equalArg a xArgs yArgs
	    (Con x xArgs, Con y yArgs)
		| x == y -> do
		    -- The type is a datatype.
		    Def d args <- reduce $ unEl t
		    -- Get the number of parameters to the datatype
		    Datatype npars _ _ _ _ _ <- theDef <$> getConstInfo d
		    -- The type to compare the arguments at is obtained by
		    -- instantiating the parameters.
		    a <- defType <$> getConstInfo x
		    let a' = piApply a (take npars args)
		    equalArg a' xArgs yArgs
	    (MetaV x xArgs, MetaV y yArgs)
		| x == y -> if   sameVars xArgs yArgs
			    then return []
			    else do -- Check syntactic equality on meta-variables
				    -- (same as for blocked terms)
			      m <- normalise m
			      n <- normalise n
			      if m == n
				then return []
				else buildConstraint (ValueEq t m n)
		| otherwise -> do
		    [p1, p2] <- mapM getMetaPriority [x,y]
		    -- instantiate later meta variables first
		    let (solve1, solve2)
			  | (p1,x) > (p2,y) = (l,r)
			  | otherwise	    = (r,l)
			  where l = assignV t x xArgs n
				r = assignV t y yArgs m
			try m fallback = do
			  cs <- m
			  case cs of
			    []	-> return []
			    _	-> fallback cs

		    -- First try the one with the highest priority. If that doesn't
		    -- work, try the low priority one. If that doesn't work either,
		    -- go with the first version.
		    rollback <- return . put =<< get
		    try solve1 $ \cs -> do
		      undoRollback <- return . put =<< get
		      rollback
		      try solve2 $ \_ -> do
			undoRollback
			return cs

	    (MetaV x xArgs, _) -> assignV t x xArgs n
	    (_, MetaV x xArgs) -> assignV t x xArgs m
	    (BlockedV _, BlockedV _)	-> do
		n <- normalise n    -- is this what we want?
		m <- normalise m
		if m == n
		    then return []	-- Check syntactic equality for blocked terms
		    else useInjectivity t m n
	    (BlockedV b, _)    -> useInjectivity t m n
	    (_,BlockedV b)     -> useInjectivity t m n
	    _		       -> typeError $ UnequalTerms m n t
    where
	equalFun (FunV arg1@(Arg h1 a1) t1) (FunV (Arg h2 a2) t2)
	    | h1 /= h2	= typeError $ UnequalHiding ty1 ty2
	    | otherwise = do
		    let (ty1',ty2') = raise 1 (ty1,ty2)
			arg	    = Arg h1 (Var 0 [])
		    name <- freshName_ (suggest t1 t2)
		    cs   <- equalType a1 a2
		    let c = TypeEq (piApply ty1' [arg]) (piApply ty2' [arg])

		    -- We only need to require a1 == a2 if t2 is a dependent function type.
		    -- If it's non-dependent it doesn't matter what we add to the context.
		    let dependent = case t2 of
					Pi _ _	-> True
					Fun _ _	-> False
					_	-> __IMPOSSIBLE__
		    if dependent
			then addCtx name arg1 $ guardConstraint (return cs) c
			else do
			    cs' <- addCtx name arg1 $ solveConstraint c
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
equalArg :: MonadTCM tcm => Type -> Args -> Args -> tcm Constraints
equalArg _ [] [] = return []
equalArg _ [] (_:_) = __IMPOSSIBLE__
equalArg _ (_:_) [] = __IMPOSSIBLE__
equalArg a (arg1 : args1) (arg2 : args2) = do
    a <- reduce a
    case funView (unEl a) of
	FunV (Arg _ b) _ -> do
	    verbose 10 $ do
		db <- prettyTCM b
		darg1 <- prettyTCM arg1
		darg2 <- prettyTCM arg2
		debug $ "equalArg " ++ show darg1 ++ "  ==  " ++ show darg2 ++ " : " ++ show db
            cs1 <- equalTerm b (unArg arg1) (unArg arg2)
	    case (cs1, unEl a) of
		(_:_, Pi _ c) | 0 `freeIn` absBody c
		    -> do
                        verbose 15 $ do
                            db <- prettyTCM b
                            darg1 <- prettyTCM arg1
                            darg2 <- prettyTCM arg2
                            dcs   <- mapM prettyTCM cs1
                            debug $ "aborting equalArg " ++ show darg1 ++ "  ==  " ++ show darg2 ++ " : " ++ show db
                            debug $ " --> " ++ show dcs
                        patternViolation   -- TODO: will duplicate work (all arguments checked so far)
		_   -> do
                    verbose 15 $ do
                        db <- prettyTCM (piApply a [arg1])
                        darg1 <- mapM prettyTCM args1
                        darg2 <- mapM prettyTCM args2
                        debug $ "equalArgs " ++ show darg1 ++ "  ==  " ++ show darg2 ++ " : " ++ show db
		    cs2 <- equalArg (piApply a [arg1]) args1 args2
		    return $ cs1 ++ cs2
        _   -> patternViolation


-- | Equality on Types
equalType :: MonadTCM tcm => Type -> Type -> tcm Constraints
equalType ty1@(El s1 a1) ty2@(El s2 a2) =
    catchConstraint (TypeEq ty1 ty2) $ do
	verbose 9 $ do
	    d1 <- prettyTCM ty1
	    d2 <- prettyTCM ty2
	    s1 <- prettyTCM s1
	    s2 <- prettyTCM s2
	    debug $ "equalType " ++ show d1 ++ "  ==  " ++ show d2
	    debug $ "   sorts: " ++ show s1 ++ "  and  " ++ show s2
	cs1 <- equalSort s1 s2
	cs2 <- equalTerm (sort s1) a1 a2
	verbose 9 $ do
	    dcs <- mapM prettyTCM $ cs1 ++ cs2
	    debug $ "   --> " ++ show dcs
	return $ cs1 ++ cs2

leqType :: MonadTCM tcm => Type -> Type -> tcm Constraints
leqType ty1@(El s1 a1) ty2@(El s2 a2) = do
     -- TODO: catchConstraint (?)
    (a1, a2) <- reduce (a1,a2)
    case (a1, a2) of
	(Sort s1, Sort s2) -> leqSort s1 s2
	_		   -> equalType (El s1 a1) (El s2 a2)
	    -- TODO: subtyping for function types

---------------------------------------------------------------------------
-- * Sorts
---------------------------------------------------------------------------

-- | Check that the first sort is less or equal to the second.
leqSort :: MonadTCM tcm => Sort -> Sort -> tcm Constraints
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
equalSort :: MonadTCM tcm => Sort -> Sort -> tcm Constraints
equalSort s1 s2 =
    catchConstraint (SortEq s1 s2) $
    do	(s1,s2) <- reduce (s1,s2)
-- 	do  d1 <- prettyTCM s1
-- 	    d2 <- prettyTCM s2
-- 	    debug $ "equalSort " ++ show d1 ++ " == " ++ show d2
	case (s1,s2) of

	    (MetaS x , MetaS y ) | x == y    -> return []
				 | otherwise -> do
		[p1, p2] <- mapM getMetaPriority [x, y]
		if p1 >= p2 then assignS x s2
			    else assignS y s1
	    (MetaS x , _       )	     -> assignS x s2
	    (_	     , MetaS x )	     -> equalSort s2 s1

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

    where
	notEq s1 s2 = typeError $ UnequalSorts s1 s2

