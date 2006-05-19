{-# OPTIONS -cpp #-}
module TypeChecking.Substitute where

import Control.Monad.Identity
import Control.Monad.Reader
import Data.Generics

import Syntax.Common
import Syntax.Internal
import Syntax.Internal.Walk

import TypeChecking.Monad

import Utils.Monad

#include "../undefined.h"

-- | Apply something to a bunch of arguments.
--   Preserves blocking tags (application can never resolve blocking).
class Apply t where
    apply :: t -> Args -> t

instance Apply Term where
    apply m args =
	case m of
	    Var i args'   -> Var i (args'++args)
	    Lam m args'   -> Lam m (args'++args)
	    Def c args'   -> Def c (args'++args)
	    Con c args'   -> Con c (args'++args)
	    MetaV x args' -> MetaV x (args'++args) 
	    BlockedV b	  -> BlockedV $ b `apply` args
	    Lit l	  -> __IMPOSSIBLE__

instance Apply Type where
    apply a []	= a
    apply (MetaT x args') args		  = MetaT x (args' ++ args)
    apply (LamT (Abs _ a)) (Arg _ v:args) = subst v a `apply` args
    apply (Sort s) _			  = __IMPOSSIBLE__
    apply (Pi _ _ _) _			  = __IMPOSSIBLE__
    apply (El _ _) _			  = __IMPOSSIBLE__

instance Apply Sort where
    apply s [] = s
    apply s _  = __IMPOSSIBLE__

instance Apply Definition where
    apply (Defn t n d@(Constructor _ _ _)) args =
	Defn (substs (map unArg args) t) n (apply d args)
    apply (Defn t n d) args = Defn (piApply t args) n (apply d args)

instance Apply Defn where
    apply Axiom _		     = Axiom
    apply (Function cs a) args	     = Function (apply cs args) a
    apply (Datatype np cs s a) args  = Datatype (np - length args) cs s a
    apply (Constructor np cs a) args = Constructor (np - length args) cs a

instance Apply Clause where
    apply (Clause ps b) args = Clause (drop (length args) ps) $ apply b args

instance Apply ClauseBody where
    apply b []				  = b
    apply (Bind (Abs _ b)) (Arg _ v:args) = subst v b `apply` args
    apply (Body _) (_:_)		  = __IMPOSSIBLE__

instance Apply t => Apply [t] where
    apply ts args = map (`apply` args) ts

instance Apply t => Apply (Blocked t) where
    apply b args = fmap (`apply` args) b

piApply :: Type -> Args -> Type
piApply t []			  = t
piApply (Pi _ _ b) (Arg _ v:args) = absApp v b `piApply` args
piApply _ _			  = __IMPOSSIBLE__

-- | @(abstract args v) args --> v[args]@.
class Abstract t where
    abstract :: Telescope -> t -> t

instance Abstract Term where
    abstract tel v = foldl (\v _ -> Lam (Abs "x" v) []) v $ reverse tel

instance Abstract Type where
    abstract tel a = foldl (\a _ -> LamT (Abs "x" a)   ) a $ reverse tel

instance Abstract Sort where
    abstract [] s = s
    abstract _ s = __IMPOSSIBLE__

instance Abstract Definition where
    abstract tel (Defn t n d@(Constructor _ _ _)) = Defn t n (abstract tel d)
    abstract tel (Defn t n d) = Defn (telePi tel t) n (abstract tel d)

instance Abstract Defn where
    abstract tel Axiom		       = Axiom
    abstract tel (Function cs a)       = Function (abstract tel cs) a
    abstract tel (Datatype np cs s a)  = Datatype (length tel + np) cs s a
    abstract tel (Constructor np cs a) = Constructor (length tel + np) cs a

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
	    Lam m vs	    -> uncurry Lam $ substAt n u (m,vs)
	    Def c vs	    -> Def c $ substAt n u vs
	    Con c vs	    -> Con c $ substAt n u vs
	    MetaV x vs	    -> MetaV x $ substAt n u vs
	    Lit l	    -> Lit l
	    BlockedV b	    -> BlockedV $ substAt n u b

instance Subst Type where
    substAt n u t =
	case t of
	    El t s     -> flip El s $ substAt n u t
	    Pi h a b   -> uncurry (Pi h) $ substAt n u (a,b)
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
    substAt n u (Body t) = Body $ substAt n u t
    substAt n u (Bind b) = Bind $ substAt n u b

-- subst :: Data a => Term -> a -> a
-- subst repl x = runIdentity $ walk (mkM goVal) x where
--   goVal (Var i args) = do
--       n <- ask
--       if i == n
--           then do 
--               args' <- mapM goArg args	-- TODO: will this traverse more than the top-level?
--               endWalk $ apply (raise n repl) args'
--           else return $ Var (if i > n then i - 1 else i) args
--   goVal x = return x
--   
--   goArg (Arg h v) = Arg h <$> goVal v

-- | Substitute a lot of terms.
substs :: Subst t => [Term] -> t -> t
substs []     x = x
substs (t:ts) x = subst t (substs (raise 1 ts) x)

-- | Instantiate an abstraction
absApp :: Subst t => Term -> Abs t -> t
absApp u (Abs _ v) = subst u v

-- | Add @k@ to index of each open variable in @x@.
--
raiseFrom :: Int -> Int -> GenericT
raiseFrom m k x = runIdentity $ walk (mkM goTm) x
    where
	goTm (Var i args) = do
	  n <- ask
	  return $ Var (newVar i n) args
	goTm x = return x

	newVar i n
	    | i >= n + m    = i + k
	    | otherwise	    = i

raise :: Int -> GenericT
raise = raiseFrom 0

