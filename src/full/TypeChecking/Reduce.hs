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
import Syntax.Scope (ModuleScope)

import TypeChecking.Monad
import TypeChecking.Monad.Context
import TypeChecking.Monad.Builtin
import TypeChecking.Substitute
import TypeChecking.Interface

#ifndef __HADDOCK__
import {-# SOURCE #-} TypeChecking.Patterns.Match
#endif

import Utils.Monad

import TypeChecking.Monad.Debug
__debug = debug

#include "../undefined.h"

-- | Instantiate something.
--   Results in an open meta variable or a non meta.
--   Doesn't do any reduction, and preserves blocking tags (when blocking meta
--   is uninstantiated).
class Instantiate t where
    instantiate :: t -> TCM t

instance Instantiate Term where
    instantiate t@(MetaV x args) =
	do  mi <- mvInstantiation <$> lookupMeta x
	    case mi of
		InstV a -> instantiate $ a `apply` args
		Open	-> return t
		_	-> __IMPOSSIBLE__
    instantiate v@(BlockedV (Blocked x u)) =
	do  mi <- mvInstantiation <$> lookupMeta x
	    case mi of
		InstV _ -> instantiate u
		Open	-> return v
		_	-> __IMPOSSIBLE__
    instantiate t = return t

instance Instantiate Type where
    instantiate t@(MetaT x args) =
	do  mi <- mvInstantiation <$> lookupMeta x
	    case mi of
		InstT t' -> instantiate $ t' `apply` args
		Open	 -> return t
		_	 -> __IMPOSSIBLE__
    instantiate t = return t

instance Instantiate Sort where
    instantiate s@(MetaS x) =
	do  mi <- mvInstantiation <$> lookupMeta x
	    case mi of
		InstS s' -> instantiate s'
		Open	 -> return s
		_	 -> __IMPOSSIBLE__
    instantiate s = return s

instance Instantiate t => Instantiate (Arg t) where
    instantiate = fmapM instantiate

instance Instantiate t => Instantiate [t] where
    instantiate = mapM instantiate

instance (Instantiate a, Instantiate b) => Instantiate (a,b) where
    instantiate (x,y) = (,) <$> instantiate x <*> instantiate y


instance (Instantiate a, Instantiate b,Instantiate c) => Instantiate (a,b,c) where
    instantiate (x,y,z) = (,,) <$> instantiate x <*> instantiate y <*> instantiate z



instance Instantiate a => Instantiate (Closure a) where
    instantiate cl = do
	x <- enterClosure cl instantiate
	return $ cl { clValue = x }

instance Instantiate Constraint where
    instantiate (ValueEq t u v) =
	do  (t,u,v) <- instantiate (t,u,v)
	    return $ ValueEq t u v
    instantiate (TypeEq a b)  = uncurry TypeEq <$> instantiate (a,b)
    instantiate (SortEq a b)  = uncurry SortEq <$> instantiate (a,b)
    instantiate (SortLeq a b) = uncurry SortLeq <$> instantiate (a,b)

instance (Ord k, Instantiate e) => Instantiate (Map k e) where
    instantiate m =
	do  let (ks,es) = unzip $ Map.toList m
	    es <- instantiate es
	    return $ Map.fromList $ zip ks es
	-- Argh! No instance FunctorM (Map k).




--
-- Reduction to weak head normal form.
--
class Reduce t where
    reduce :: t -> TCM t

instance Reduce Type where
    reduce a =
	{-# SCC "reduce<Type>" #-}
	do  b <- instantiate a
	    case b of
		El t s	  -> El <$> reduce t <*> reduce s
		Sort s	  -> Sort <$> reduce s
		Pi _ _	  -> return b
		Fun _ _   -> return b
		MetaT _ _ -> return b
		LamT _	  -> __IMPOSSIBLE__

instance Reduce Sort where
    reduce s =
	{-# SCC "reduce<Sort>" #-}
	do  s <- instantiate s
	    case s of
		Suc s'	  -> sSuc <$> reduce s'
		Lub s1 s2 -> sLub <$> reduce s1 <*> reduce s2
		Prop	  -> return s
		Type _	  -> return s
		MetaS _   -> return s

instance Reduce t => Reduce [t] where
    reduce = mapM reduce

instance Reduce t => Reduce (Arg t) where
    reduce = fmapM reduce

instance (Reduce a, Reduce b) => Reduce (a,b) where
    reduce (x,y) = (,) <$> reduce x <*> reduce y

instance (Reduce a, Reduce b,Reduce c) => Reduce (a,b,c) where
    reduce (x,y,z) = (,,) <$> reduce x <*> reduce y <*> reduce z

instance Reduce Term where
    reduce v =
	{-# SCC "reduce<Term>" #-}
	do  v <- instantiate v
	    case v of
		MetaV x args -> MetaV x <$> reduce args
		Def f args   -> reduceDef (Def f []) f args
		Con c args   -> reduceDef (Con c []) c args
						-- constructors can have definitions
						-- when they come from an instantiated module
						-- (change this)
		BlockedV _ -> return v
		Lit _	   -> return v
		Var _ _	   -> return v
		Lam _ _	   -> return v
	where

	    reduceDef v0 f args =
		{-# SCC "reduceDef" #-}
		do  info <- getConstInfo f
		    case info of
			Defn _ _ (Primitive ConcreteDef x) -> do
			    pf <- getPrimitive x
			    reducePrimitive v0 f args pf
			_				   -> reduceNormal v0 f args $ defClauses info

	    reducePrimitive v0 f args pf
		| n < ar    = return $ v0 `apply` args	-- not fully applied
		| otherwise = do
		    let (args1,args2) = splitAt n args
		    r <- def args1
		    case r of
			NoReduction args1'  -> return $ v0 `apply` (args1' ++ args2)
			YesReduction v	    -> reduce $ v  `apply` args2
		where
		    n	= length args
		    ar  = primFunArity pf
		    def = primFunImplementation pf

	    reduceNormal v0 f args def = do
		    def <- defClauses <$> getConstInfo f
		    case def of
			[] -> return $ v0 `apply` args -- no definition for head
			cls@(Clause ps _ : _)
			    | length ps <= length args ->
				do  let (args1,args2) = splitAt (length ps) args 
				    ev <- appDef v0 cls args1
				    case ev of
					NoReduction v  -> return $ v `apply` args2
					YesReduction v -> reduce $ v `apply` args2
			    | otherwise	-> return $ v0 `apply` args -- partial application

	    -- Apply a defined function to it's arguments.
	    --   The original term is the first argument applied to the third.
	    appDef :: Term -> [Clause] -> Args -> TCM (Reduced Term Term)
	    appDef v cls args = goCls cls args where

		goCls [] _ = fail $ "incomplete patterns for " ++ show v
		goCls (cl@(Clause pats body) : cls) args =
		    do	(m, args) <- matchPatterns pats args
			case m of
			    Yes args'	      -> return $ YesReduction $ app args' body
			    No		      -> goCls cls args
			    DontKnow Nothing  -> return $ NoReduction $ v `apply` args
			    DontKnow (Just m) -> return $ NoReduction $ blocked m $ v `apply` args

		app []		 (Body v')	     = v'
		app (arg : args) (Bind (Abs _ body)) = app args $ subst arg body -- CBN
		app (_   : args) (NoBind body)	     = app args body
		app  _		  NoBody	     = __IMPOSSIBLE__
		app (_ : _)	 (Body _)	     = __IMPOSSIBLE__
		app []		 (Bind _)	     = __IMPOSSIBLE__
		app []		 (NoBind _)	     = __IMPOSSIBLE__


instance Reduce a => Reduce (Closure a) where
    reduce cl = do
	x <- enterClosure cl reduce
	return $ cl { clValue = x }

instance Reduce Constraint where
    reduce (ValueEq t u v) =
	do  (t,u,v) <- reduce (t,u,v)
	    return $ ValueEq t u v
    reduce (TypeEq a b)  = uncurry TypeEq <$> reduce (a,b)
    reduce (SortEq a b)  = uncurry SortEq <$> reduce (a,b)
    reduce (SortLeq a b) = uncurry SortLeq <$> reduce (a,b)

instance (Ord k, Reduce e) => Reduce (Map k e) where
    reduce m =
	do  let (ks,es) = unzip $ Map.toList m
	    es <- reduce es
	    return $ Map.fromList $ zip ks es
	-- Argh! No instance FunctorM (Map k).


---------------------------------------------------------------------------
-- * Normalisation
---------------------------------------------------------------------------

class Normalise t where
    normalise :: t -> TCM t

instance Normalise Sort where
    normalise = reduce

instance Normalise Type where
    normalise t =
	do  t <- reduce t
	    case t of
		El v s	   -> El <$> normalise v <*> normalise s
		Sort s	   -> Sort <$> normalise s
		Pi a b	   -> uncurry Pi <$> normalise (a,b)
		Fun a b    -> uncurry Fun <$> normalise (a,b)
		MetaT x vs -> MetaT x <$> normalise vs
		LamT _	   -> __IMPOSSIBLE__

instance Normalise Term where
    normalise v =
	do  v <- reduce v
	    case ignoreBlocking v of
		Var n vs    -> Var n <$> normalise vs
		Con c vs    -> Con c <$> normalise vs
		Def f vs    -> Def f <$> normalise vs
		MetaV x vs  -> MetaV x <$> normalise vs
		Lit _	    -> return v
		Lam h b	    -> Lam h <$> normalise b
		BlockedV _  -> __IMPOSSIBLE__

instance Normalise ClauseBody where
    normalise (Body   t) = Body   <$> normalise t
    normalise (Bind   b) = Bind   <$> normalise b
    normalise (NoBind b) = NoBind <$> normalise b
    normalise  NoBody	 = return NoBody

instance Normalise t => Normalise (Abs t) where
    normalise = fmapM normalise

instance Normalise t => Normalise (Arg t) where
    normalise = fmapM normalise

instance Normalise t => Normalise [t] where
    normalise = fmapM normalise

instance (Normalise a, Normalise b) => Normalise (a,b) where
    normalise (x,y) = (,) <$> normalise x <*> normalise y

instance (Normalise a, Normalise b, Normalise c) => Normalise (a,b,c) where
    normalise (x,y,z) =
	do  (x,(y,z)) <- normalise (x,(y,z))
	    return (x,y,z)

instance Normalise a => Normalise (Closure a) where
    normalise cl = do
	x <- enterClosure cl normalise
	return $ cl { clValue = x }

instance Normalise Constraint where
    normalise (ValueEq t u v) =
	do  (t,u,v) <- normalise (t,u,v)
	    return $ ValueEq t u v
    normalise (TypeEq a b)  = uncurry TypeEq <$> normalise (a,b)
    normalise (SortEq a b)  = uncurry SortEq <$> normalise (a,b)
    normalise (SortLeq a b) = uncurry SortLeq <$> normalise (a,b)

instance (Ord k, Normalise e) => Normalise (Map k e) where
    normalise m =
	do  let (ks,es) = unzip $ Map.toList m
	    es <- normalise es
	    return $ Map.fromList $ zip ks es
	-- Argh! No instance FunctorM (Map k).

---------------------------------------------------------------------------
-- * Full instantiation
---------------------------------------------------------------------------

-- Full instantiatiation = normalisation [ instantiate / reduce ]
-- How can we express this? We need higher order classes!

class InstantiateFull t where
    instantiateFull :: t -> TCM t

instance InstantiateFull Sort where
    instantiateFull = instantiate

instance InstantiateFull Type where
    instantiateFull t =
	do  t <- instantiate t
	    case t of
		El v s	   -> El <$> instantiateFull v <*> instantiateFull s
		Sort s	   -> Sort <$> instantiateFull s
		Pi a b	   -> uncurry Pi <$> instantiateFull (a,b)
		Fun a b    -> uncurry Fun <$> instantiateFull (a,b)
		MetaT x vs -> MetaT x <$> instantiateFull vs
		LamT _	   -> __IMPOSSIBLE__

instance InstantiateFull Term where
    instantiateFull v =
	do  v <- instantiate v
	    case ignoreBlocking v of
		Var n vs    -> Var n <$> instantiateFull vs
		Con c vs    -> Con c <$> instantiateFull vs
		Def f vs    -> Def f <$> instantiateFull vs
		MetaV x vs  -> MetaV x <$> instantiateFull vs
		Lit _	    -> return v
		Lam h b	    -> Lam h <$> instantiateFull b
		BlockedV _  -> __IMPOSSIBLE__

instance InstantiateFull ClauseBody where
    instantiateFull (Body   t) = Body   <$> instantiateFull t
    instantiateFull (Bind   b) = Bind   <$> instantiateFull b
    instantiateFull (NoBind b) = NoBind <$> instantiateFull b
    instantiateFull  NoBody    = return NoBody

instance InstantiateFull t => InstantiateFull (Abs t) where
    instantiateFull = fmapM instantiateFull

instance InstantiateFull t => InstantiateFull (Arg t) where
    instantiateFull = fmapM instantiateFull

instance InstantiateFull t => InstantiateFull [t] where
    instantiateFull = fmapM instantiateFull

instance (InstantiateFull a, InstantiateFull b) => InstantiateFull (a,b) where
    instantiateFull (x,y) = (,) <$> instantiateFull x <*> instantiateFull y

instance (InstantiateFull a, InstantiateFull b, InstantiateFull c) => InstantiateFull (a,b,c) where
    instantiateFull (x,y,z) =
	do  (x,(y,z)) <- instantiateFull (x,(y,z))
	    return (x,y,z)

instance InstantiateFull a => InstantiateFull (Closure a) where
    instantiateFull cl = do
	x <- enterClosure cl instantiateFull
	return $ cl { clValue = x }

instance InstantiateFull Constraint where
    instantiateFull (ValueEq t u v) =
	do  (t,u,v) <- instantiateFull (t,u,v)
	    return $ ValueEq t u v
    instantiateFull (TypeEq a b)  = uncurry TypeEq <$> instantiateFull (a,b)
    instantiateFull (SortEq a b)  = uncurry SortEq <$> instantiateFull (a,b)
    instantiateFull (SortLeq a b) = uncurry SortLeq <$> instantiateFull (a,b)

instance (Ord k, InstantiateFull e) => InstantiateFull (Map k e) where
    instantiateFull m =
	do  let (ks,es) = unzip $ Map.toList m
	    es <- instantiateFull es
	    return $ Map.fromList $ zip ks es
	-- Argh! No instance FunctorM (Map k).

instance InstantiateFull ModuleName where
    instantiateFull = return

instance InstantiateFull ModuleScope where
    instantiateFull = return

instance InstantiateFull ModuleDef where
    instantiateFull (ModuleDef n tel p d) =
	ModuleDef n <$> instantiateFull tel
		    <*> return p
		    <*> instantiateFull d

instance InstantiateFull Char where
    instantiateFull = return

instance InstantiateFull Definition where
    instantiateFull (Defn t n d) =
	Defn <$> instantiateFull t
	     <*> return n
	     <*> instantiateFull d

instance InstantiateFull Defn where
    instantiateFull d = case d of
	Axiom		  -> return Axiom
	Function cs a	  -> flip Function a <$> instantiateFull cs
	Datatype n cs s a -> do
	    s <- instantiateFull s
	    return $ Datatype n cs s a
	Constructor n q a -> return $ Constructor n q a
	Primitive a s	  -> return $ Primitive a s

instance InstantiateFull Clause where
    instantiateFull (Clause ps b) = Clause ps <$> instantiateFull b

instance InstantiateFull Interface where
    instantiateFull (Interface v ms scope sig isig b) =
	Interface v ms scope
	    <$> instantiateFull sig
	    <*> instantiateFull isig
	    <*> instantiateFull b

instance InstantiateFull a => InstantiateFull (Builtin a) where
    instantiateFull (Builtin t) = Builtin <$> instantiateFull t
    instantiateFull (Prim x)	= Prim <$> instantiateFull x


