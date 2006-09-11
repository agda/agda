{-# OPTIONS -cpp #-}
module TypeChecking.Substitute where

import Control.Monad.Identity
import Control.Monad.Reader
import Data.Generics
import Data.Map (Map)

import Syntax.Common
import Syntax.Internal
import Syntax.Internal.Walk

import TypeChecking.Monad.Base

import Utils.Monad

#include "../undefined.h"

-- | Apply something to a bunch of arguments.
--   Preserves blocking tags (application can never resolve blocking).
class Apply t where
    apply :: t -> Args -> t

instance Apply Term where
    apply m [] = m
    apply m args@(Arg _ v:args0) =
	case m of
	    Var i args'   -> Var i (args'++args)
	    Def c args'   -> Def c (args'++args)
	    Con c args'   -> Con c (args'++args)
	    Lam _ u	  -> absApp u v `apply` args0
	    MetaV x args' -> MetaV x (args'++args) 
	    BlockedV b	  -> BlockedV $ b `apply` args
	    Lit l	  -> __IMPOSSIBLE__

instance Apply Type where
    apply a []	= a
    apply (MetaT x args') args	  = MetaT x (args' ++ args)
    apply (LamT a) (Arg _ v:args) = absApp a v `apply` args
    apply (Sort s) _		  = __IMPOSSIBLE__
    apply (Pi _ _) _		  = __IMPOSSIBLE__
    apply (Fun _ _) _		  = __IMPOSSIBLE__
    apply (El _ _) _		  = __IMPOSSIBLE__

instance Apply Sort where
    apply s [] = s
    apply s _  = __IMPOSSIBLE__

instance Apply Definition where
    apply (Defn t n d) args = Defn (piApply t args) (n - length args) (apply d args)

instance Apply Defn where
    apply Axiom _		     = Axiom
    apply (Function cs a) args	     = Function (apply cs args) a
    apply (Datatype np cs s a) args  = Datatype (np - length args) cs s a
    apply (Constructor np cs a) args = Constructor (np - length args) cs a
    apply (Primitive a pf) args	     = Primitive a $ pf `apply` args

instance Apply PrimFun where
    apply (PrimFun ar def) args	= PrimFun (ar - length args) $ \vs -> def (args ++ vs)

instance Apply Clause where
    apply (Clause ps b) args = Clause (drop (length args) ps) $ apply b args

instance Apply ClauseBody where
    apply b []				  = b
    apply (Bind (Abs _ b)) (Arg _ v:args) = subst v b `apply` args
    apply (NoBind b) (_:args)		  = b `apply` args
    apply (Body _) (_:_)		  = __IMPOSSIBLE__

instance Apply t => Apply [t] where
    apply ts args = map (`apply` args) ts

instance Apply t => Apply (Blocked t) where
    apply b args = fmap (`apply` args) b

instance (Apply a, Apply b) => Apply (a,b) where
    apply (x,y) args = (apply x args, apply y args)

instance (Apply a, Apply b, Apply c) => Apply (a,b,c) where
    apply (x,y,z) args = (apply x args, apply y args, apply z args)

piApply :: Type -> Args -> Type
piApply t []			 = t
piApply (Pi  _ b) (Arg _ v:args) = absApp b v `piApply` args
piApply (Fun _ b) (_:args)	 = b
piApply _ _			 = __IMPOSSIBLE__

-- | @(abstract args v) args --> v[args]@.
class Abstract t where
    abstract :: Telescope -> t -> t

instance Abstract Term where
    abstract tel v = foldl (\v (Arg h _) -> Lam h (Abs "x" v)) v $ reverse tel

instance Abstract Type where
    abstract tel a = foldl (\a _ -> LamT (Abs "x" a)   ) a $ reverse tel

instance Abstract Sort where
    abstract [] s = s
    abstract _ s = __IMPOSSIBLE__

instance Abstract Definition where
    abstract tel (Defn t n d) = Defn (telePi tel t) (length tel + n) (abstract tel d)

instance Abstract Defn where
    abstract tel Axiom		       = Axiom
    abstract tel (Function cs a)       = Function (abstract tel cs) a
    abstract tel (Datatype np cs s a)  = Datatype (length tel + np) cs s a
    abstract tel (Constructor np cs a) = Constructor (length tel + np) cs a
    abstract tel (Primitive a pf)      = Primitive a $ abstract tel pf

instance Abstract PrimFun where
    abstract tel (PrimFun ar def)      = PrimFun (ar + n) $ \ts -> def $ drop n ts
	where n = length tel

instance Abstract Clause where
    abstract tel (Clause ps b) = Clause (ps0 ++ ps) $ abstract tel b
	where
	    ps0 = map (fmap $ const $ VarP "_") tel

instance Abstract ClauseBody where
    abstract []	     b = b
    abstract (_:tel) b = Bind $ Abs "x" $ abstract tel b

instance Abstract t => Abstract [t] where
    abstract tel = map (abstract tel)

-- | Substitute a term for the nth free variable.
--
class Subst t where
    substAt :: Int -> Term -> t -> t

subst :: Subst t => Term -> t -> t
subst u t = substAt 0 u t

instance Subst Term where
    substAt n u t =
	case t of
	    Var i vs
		| i < n	    -> Var i $ substAt n u vs
		| i == n    -> u `apply` substAt n u vs
		| otherwise -> Var (i - 1) $ substAt n u vs
	    Lam h m	    -> Lam h $ substAt n u m
	    Def c vs	    -> Def c $ substAt n u vs
	    Con c vs	    -> Con c $ substAt n u vs
	    MetaV x vs	    -> MetaV x $ substAt n u vs
	    Lit l	    -> Lit l
	    BlockedV b	    -> BlockedV $ substAt n u b

instance Subst Type where
    substAt n u t =
	case t of
	    El t s     -> flip El s $ substAt n u t
	    Pi a b     -> uncurry Pi $ substAt n u (a,b)
	    Fun a b    -> uncurry Fun $ substAt n u (a,b)
	    Sort s     -> Sort s
	    MetaT x vs -> MetaT x $ substAt n u vs
	    LamT b     -> LamT $ substAt n u b

instance Subst t => Subst (Blocked t) where
    substAt n u b = fmap (substAt n u) b

instance (Data a, Subst a) => Subst (Abs a) where
    substAt n u (Abs x t) = Abs x $ substAt (n + 1) (raise 1 u) t

instance Subst a => Subst (Arg a) where
    substAt n u = fmap (substAt n u)

instance Subst a => Subst [a] where
    substAt n u = map (substAt n u)

instance (Subst a, Subst b) => Subst (a,b) where
    substAt n u (x,y) = (substAt n u x, substAt n u y)

instance Subst ClauseBody where
    substAt n u (Body t)   = Body $ substAt n u t
    substAt n u (Bind b)   = Bind $ substAt n u b
    substAt n u (NoBind b) = NoBind $ substAt n u b

-- | Substitute a lot of terms.
-- substs :: Subst t => [Term] -> t -> t
-- substs []     x = x
-- substs (t:ts) x = subst t (substs (raise 1 ts) x)

-- | Instantiate an abstraction
absApp :: Subst t => Abs t -> Term -> t
absApp (Abs _ v) u = subst u v

-- | Add @k@ to index of each open variable in @x@.
class Raise t where
    raiseFrom :: Int -> Int -> t -> t

instance Raise Term where
    raiseFrom m k v =
	case v of
	    Var i vs
		| i < m	    -> Var i $ rf vs
		| otherwise -> Var (i + k) $ rf vs
	    Lam h m	    -> Lam h $ rf m
	    Def c vs	    -> Def c $ rf vs
	    Con c vs	    -> Con c $ rf vs
	    MetaV x vs	    -> MetaV x $ rf vs
	    Lit l	    -> Lit l
	    BlockedV b	    -> BlockedV $ rf b
	where
	    rf x = raiseFrom m k x

instance Raise Type where
    raiseFrom m k t =
	case t of
	    El t s     -> flip El s $ rf t
	    Pi a b     -> uncurry Pi $ rf (a,b)
	    Fun a b    -> uncurry Fun $ rf (a,b)
	    Sort s     -> Sort s
	    MetaT x vs -> MetaT x $ rf vs
	    LamT b     -> LamT $ rf b
	where
	    rf x = raiseFrom m k x

instance Raise t => Raise (Abs t) where
    raiseFrom m k = fmap (raiseFrom (m + 1) k)

instance Raise t => Raise (Arg t) where
    raiseFrom m k = fmap (raiseFrom m k)

instance Raise t => Raise (Blocked t) where
    raiseFrom m k = fmap (raiseFrom m k)

instance Raise t => Raise [t] where
    raiseFrom m k = fmap (raiseFrom m k)

instance Raise v => Raise (Map k v) where
    raiseFrom m k = fmap (raiseFrom m k)

instance (Raise a, Raise b) => Raise (a,b) where
    raiseFrom m k (x,y) = (raiseFrom m k x, raiseFrom m k y)

raise :: Raise t => Int -> t -> t
raise = raiseFrom 0

