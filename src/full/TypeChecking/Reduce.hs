{-# OPTIONS -cpp #-}

{-| TODO: take care of hidden arguments -}
module TypeChecking.Reduce where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Identity
import Data.List as List
import Data.Map as Map
import Data.Generics

import Syntax.Common
import Syntax.Internal
import Syntax.Internal.Walk

import TypeChecking.Monad
import TypeChecking.Monad.Context
import TypeChecking.Substitute

import TypeChecking.Monad.Debug
__debug = debug

#include "../undefined.h"

refresh :: Data a => a -> TCM a
refresh = walk (mkM refType `extM` refTerm `extM` refSort)
    where
	refType = lift . lift . instType
	refTerm = lift . lift . reduceM
	refSort = lift . lift . instSort

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
--   Taking this function out of the monad allows us to get
--     call-by-need semantics for free.
--   Arguments are not evaluated until just before being substituted.
--     So @reduce st ctx sig (c m1 m2) == c m1 m2@ when @c@ is an 
--     undefined constant.
--
reduce :: TCEnv -> MetaStore -> Context -> Signature -> Term -> Term
reduce env store ctx sig v = go v where
    go v = case v of
        Lam (Abs _ v') (Arg h arg:args) -> go $ subst (go arg) v' `apply` args
        MetaV x args -> case Map.lookup x store of
            Just (InstV v) -> go $ v `apply` args
            Just _	   -> v
	    _		   -> __IMPOSSIBLE__
        Def f args -> case defOfConst f of
            [] -> v -- no definition for head
            cls@(Clause ps _ : _) -> 
                if length ps == length args then appDef v cls args  -- no-go here
                else if length ps < length args then
                    let (args1,args2) = splitAt (length ps) args 
                    in go $ appDef v cls args1 `apply` args2	    -- and go here
                else v -- partial application
        _ -> v

    -- get definition of a constant (i.e. a list of clauses)
    --
    defOfConst :: QName -> [Clause]
    defOfConst q = 
	case makeAbstract' env q =<< Map.lookup q sig of
	    Just d  -> defClauses d
	    Nothing -> __IMPOSSIBLE__

    -- Apply a defined function to it's arguments.
    --   First arg is original value which is needed in case no clause matches.
    --
    appDef :: Term -> [Clause] -> Args -> Term
    appDef v cls args = goCls cls args where
        goCls [] _ = v -- no clause matched, can happen with parameter arguments
        goCls (cl@(Clause pats body) : cls) args =
            case matchPats [] pats args of
                Just args' -> app args' body
                Nothing -> goCls cls args
        app [] (Body v') = go v'
        app (arg : args) (Bind (Abs _ body)) = app args $ subst (go arg) body
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
        case go arg of 
            Con c' args | c' == c -> matchPats curArgs pats args 
            _ -> Nothing

-- | Monadic version of reduce.
--
reduceM :: Term -> TCM Term
reduceM v = do
    store <- gets stMetaStore
    ctx   <- asks envContext
    sig   <- gets stSignature
    env	  <- ask
    return $ reduce env store ctx sig v

