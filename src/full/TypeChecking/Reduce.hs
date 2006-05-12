{-# OPTIONS -cpp #-}

{-| TODO: take care of hidden arguments -}
module TypeChecking.Reduce where

import Control.Monad.State
import Control.Monad.Reader
import Data.List as List
import Data.Map as Map
import Data.Generics

import Syntax.Common
import Syntax.Internal
import Syntax.Internal.Walk

import TypeChecking.Monad
import TypeChecking.Monad.Context
import TypeChecking.Substitute

import Utils.Monad

import TypeChecking.Monad.Debug
__debug = debug

#include "../undefined.h"

refresh :: Data a => a -> TCM a
refresh = walk (mkM refType `extM` refTerm `extM` refSort)
    where
	refType = lift . lift . instType
	refTerm = lift . lift . reduce
	refSort = lift . lift . instSort

-- | instantiate a term
--   results in an open meta variable or a non meta term.
--   Doesn't do any reduction.
instTerm :: Term -> TCM Term
instTerm a =
    case a of
	MetaV x args ->
	    do	store <- gets stMetaStore
		case Map.lookup x store of
		    Just (InstV a') -> instTerm $ a' `apply` args
		    Just _	    -> return a
		    _		    -> __IMPOSSIBLE__
	_ -> return a

-- | instantiate a type 
--   results is open meta variable or a non meta variable type.
--
instType :: Type -> TCM Type
instType a = case a of
    (MetaT x args) -> do 
        store <- gets stMetaStore
        case Map.lookup x store of
            Just (InstT a') -> instType $ reduceType a' args
            Just _          -> return a
	    Nothing	    -> __IMPOSSIBLE__
    _ -> return a

reduceType :: Type -> Args -> Type
reduceType a [] = a
reduceType a (Arg _ v : args) =
    case a of
	LamT (Abs _ a) -> reduceType (subst v a) args
	_	       -> __IMPOSSIBLE__

-- | instantiate a sort 
--   results is open meta variable or a non meta variable sort.
--
instSort :: Sort -> TCM Sort
instSort s = case s of
    (MetaS x) -> do 
        store <- gets stMetaStore
        case Map.lookup x store of
            Just (InstS s') -> instSort s'
            Just _          -> return s
	    _		    -> __IMPOSSIBLE__
    _ -> return s

--
-- Reduction
--

-- | Reduce a value to head-normal form.
--   Arguments are not evaluated until just before being substituted.
--     So @reduce st ctx sig (c m1 m2) == c m1 m2@ when @c@ is an 
--     undefined constant.
--
reduce :: Term -> TCM Term
reduce v = go v where
    go v =
	do  v <- instTerm v
	    case v of
		Lam (Abs _ v') (Arg h arg:args) ->
		    do	a <- go arg
			go $ subst a v' `apply` args
		MetaV _ _ -> return v
		Def f args ->
		    do	def <- defClauses <$> getConstInfo f
			case def of
			    [] -> return v -- no definition for head
			    cls@(Clause ps _ : _) -> 
				if length ps == length args then
				    do	ev <- appDef v cls args
					either return go ev
				else if length ps < length args then
				    let (args1,args2) = splitAt (length ps) args 
				    in do   ev <- appDef v cls args1
					    case ev of
						Left v	-> return v
						Right v	-> go $ v `apply` args2
				else return v -- partial application
		Con c args ->
		    do	c' <- canonicalConstructor c
			return $ Con c' args
		_ -> return v

    -- Apply a defined function to it's arguments.
    --   First arg is original value which is needed in case no clause matches.
    --	 'Left' means no match and 'Right' means match.
    appDef :: Term -> [Clause] -> Args -> TCM (Either Term Term)
    appDef v cls args = goCls cls =<< (fmapM . fmapM) go args where
        goCls [] _ = return $ Left v -- no clause matched, can happen with parameter arguments
        goCls (cl@(Clause pats body) : cls) args =
	    case matchPats [] pats args of
		Just args' -> Right <$> app args' body
		Nothing -> goCls cls args
        app [] (Body v') = return v'
        app (arg : args) (Bind (Abs _ body)) =
	    do	v <- go arg	-- call by value
		app args $ subst v body
	app _ _ = __IMPOSSIBLE__
	

    -- Match the given patterns to the given arguments.
    --   Returns updated list of values to instantiate the
    --     bound variables in the patterns.
    -- TODO: data Match = Yes [Term] | No | DontKnow
    matchPats :: [Term] -> [Arg Pattern] -> Args -> Maybe [Term]
    matchPats curArgs (Arg _ pat:pats) (Arg _ arg:args) = do
        newArgs <- matchPat curArgs pat arg 
        matchPats newArgs pats args
    matchPats curArgs [] [] = Just curArgs
    matchPats _ _ _ = __IMPOSSIBLE__

    matchPat :: [Term] -> Pattern -> Term -> Maybe [Term]
    matchPat curArgs (VarP x) arg = Just $ curArgs++[arg]
    matchPat curArgs (ConP c pats) arg =
        case arg of 
            Con c' args | c' == c -> matchPats curArgs pats args 
            _ -> Nothing

