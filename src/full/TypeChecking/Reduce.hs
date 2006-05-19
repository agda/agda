{-# OPTIONS -cpp -fglasgow-exts #-}

{-| TODO: take care of hidden arguments -}
module TypeChecking.Reduce where

import Control.Monad.State
import Control.Monad.Reader
import Data.List as List
import Data.Map as Map
import Data.Generics
import Data.FunctorM

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

normalise :: Data a => a -> TCM a
normalise = walk (mkM redType `extM` redTerm `extM` redSort)
    where
	redTerm :: Term -> WalkT TCM Term
	redTerm = lift . lift . reduce

	redType :: Type -> WalkT TCM Type
	redType = lift . lift . reduce

	redSort :: Sort -> WalkT TCM Sort
	redSort = lift . lift . reduce

-- | Instantiate something.
--   Results in an open meta variable or a non meta.
--   Doesn't do any reduction.
class Instantiate t where
    instantiate :: t -> TCM t

instance Instantiate Term where
    instantiate t@(MetaV x args) =
	do  mv <- lookupMeta x
	    case mv of
		InstV _ a' _ -> instantiate $ a' `apply` args
		_	     -> return t
    instantiate t = return t

instance Instantiate Type where
    instantiate t@(MetaT x args) =
	do  mv <- lookupMeta x
	    case mv of
		InstT _ a' -> instantiate $ a' `apply` args
		_	       -> return t
    instantiate t = return t

instance Instantiate Sort where
    instantiate s@(MetaS x) =
	do  mv <- lookupMeta x
	    case mv of
		InstS _ s' -> instantiate s'
		_	   -> return s
    instantiate s = return s

instance Instantiate t => Instantiate (Arg t) where
    instantiate = fmapM instantiate

instance Instantiate t => Instantiate [t] where
    instantiate = mapM instantiate

--
-- Reduction to weak head normal form.
--
class Reduce t where
    reduce :: t -> TCM t

instance Reduce Type where
    reduce a =
	do  b <- instantiate a
	    case b of
		El t s -> El <$> reduce t <*> reduce s
		Sort s -> Sort <$> reduce s
		_      -> return b

instance Reduce Sort where
    reduce s =
	do  s <- instantiate s
	    case s of
		Suc s'	  -> sSuc <$> reduce s'
		Lub s1 s2 -> sLub <$> reduce s1 <*> reduce s2
		_	  -> return s

instance Reduce Term where
    reduce v = go v where
	go v =
	    do  v <- instantiate v
		case v of
		    Lam (Abs _ v') (Arg h arg:args) ->
			do  a <- go arg
			    go $ subst a v' `apply` args
		    MetaV _ _ -> return v
		    Def f args ->
			do  def <- defClauses <$> getConstInfo f
			    case def of
				[] -> return v -- no definition for head
				cls@(Clause ps _ : _) -> 
				    if length ps == length args then
					do  ev <- appDef v cls args
					    either return go ev
				    else if length ps < length args then
					let (args1,args2) = splitAt (length ps) args 
					in do   ev <- appDef v cls args1
						case ev of
						    Left v	-> return v
						    Right v	-> go $ v `apply` args2
				    else return v -- partial application
		    Con c args ->
			do  c' <- canonicalConstructor c
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
		do  v <- go arg	-- call by value
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

