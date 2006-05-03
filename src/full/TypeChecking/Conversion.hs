{-# OPTIONS -cpp #-}

module TypeChecking.Conversion where

import Data.Generics

import Syntax.Internal
import TypeChecking.Monad
import TypeChecking.Monad.Context
import TypeChecking.MetaVars
import TypeChecking.Substitute
import TypeChecking.Reduce
import TypeChecking.Constraints

#include "../undefined.h"

-- | Equality of two instances of the same metavar
--
equalSameVar :: Data a => 
                (MetaId -> a) -> (a -> MetaVariable) -> MetaId -> [Value] -> [Value] -> TCM ()
equalSameVar meta inst x args1 args2 =
    if length args1 == length args2 then do
        -- next 2 checks could probably be nicely merged into construction 
        --   of newArgs using ListT, but then can't use list comprehension.
        checkArgs x args1 
        checkArgs x args2 
        let idx = [0 .. length args1 - 1]
        let newArgs = [Var n [] | (n, (a,b)) <- zip idx $ zip args1 args2, a === b]
        v <- newMetaSame x args1 meta -- !!! is args1 right here?
        setRef Why x $ inst $ abstract args1 (addArgs newArgs v)
    else fail $ "equalSameVar"
    where
	Var i [] === Var j [] = i == j
	v1       === v2       = False


-- | Type directed equality on values.
--
equalVal :: Data a => a -> Type -> Value -> Value -> TCM ()
equalVal _ a m n = do --trace ("equalVal ("++(show a)++") ("++(show m)++") ("++(show n)++")\n") $ do
    a' <- instType a
    case a' of
        Pi a (Abs x b) -> 
            let p = Var 0 []
                m' = raise 1 m
                n' = raise 1 n
            in do name <- freshName_ x
		  addCtx name a $ equalVal Why b (addArgs [p] m') (addArgs [p] n')
        MetaT x _ -> addCnstr x (ValueEq a m n)
        _ -> catchConstr (ValueEq a' m n) $ equalAtm Why m n

-- | Syntax directed equality on atomic values
--
equalAtm :: Data a => a -> Value -> Value -> TCM ()
equalAtm _ m n = do
    mVal <- reduceM m  -- need mVal for the metavar case
    nVal <- reduceM n  -- need nVal for the metavar case
    --trace ("equalAtm ("++(show mVal)++") ("++(show nVal)++")\n") $ 
    case (mVal, nVal) of
        (Lit l1, Lit l2) | l1 == l2 -> return ()
        (Var i iArgs, Var j jArgs) | i == j -> do
            a <- typeOfBV i
            equalArg Why a iArgs jArgs
        (Def x xArgs, Def y yArgs) | x == y -> do
            a <- typeOfConst x
            equalArg Why a xArgs yArgs
        (MetaV x xArgs, MetaV y yArgs) | x == y -> equalSameVar (\x -> MetaV x []) InstV x xArgs yArgs -- !!! MetaV args???
        (MetaV x xArgs, _) -> assign x xArgs nVal
        (_, MetaV x xArgs) -> assign x xArgs mVal
        _ -> fail $ "equalAtm "++(show m)++" ==/== "++(show n)


-- | Type-directed equality on argument lists
--
equalArg :: Data a => a -> Type -> [Value] -> [Value] -> TCM ()
equalArg _ a args1 args2 = do
    a' <- instType a
    case (a', args1, args2) of 
        (_, [], []) -> return ()
        (Pi b (Abs _ c), (arg1 : args1), (arg2 : args2)) -> do
            equalVal Why b arg1 arg2
            equalArg Why (subst arg1 c) args1 args2
        _ -> fail $ "equalArg "++(show a)++" "++(show args1)++" "++(show args2)


-- | Equality on Types
--   Assumes @Type@s being compared are at the same @Sort@
--   !!! Safe to not have @LamT@ case? @LamT@s shouldn't surface?
--
equalTyp :: Data a => a -> Type -> Type -> TCM ()
equalTyp _ a1 a2 = do
    a1' <- instType a1
    a2' <- instType a2
    case (a1', a2') of
        (El m1 s1, El m2 s2) ->
            equalVal Why (sort s1) m1 m2
        (Pi a1 (a2), Pi b1 (b2)) -> do
            equalTyp Why a1 b1
            let Abs x a2' = raise 1 a2
            let Abs _ b2' = raise 1 b2
	    name <- freshName_ x
            addCtx name a1 $ equalTyp Why (subst (Var 0 []) a2') (subst (Var 0 []) b2')
				-- TODO: this looks dangerous.. what does subst really do?
        (Sort s1, Sort s2) -> return ()
        (MetaT x xDeps, MetaT y yDeps) | x == y -> 
            equalSameVar (\x -> MetaT x []) InstT x xDeps yDeps -- !!! MetaT???
        (MetaT x xDeps, a) -> assign x xDeps a 
        (a, MetaT x xDeps) -> assign x xDeps a 
	(LamT _, _) -> __IMPOSSIBLE__
	(El _ _, _) -> fail "not equal"
	(Pi _ _, _) -> fail "not equal"
	(Sort _, _) -> fail "not equal"

