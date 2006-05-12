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
class Apply t where
    apply :: t -> Args -> t

instance Apply Term where
    apply m args =
	case m of
	    Var i args' -> Var i (args'++args)
	    Lam m args' -> Lam m (args'++args)
	    Def c args' -> Def c (args'++args)
	    Con c args' -> Con c (args'++args)
	    MetaV x args' -> MetaV x (args'++args) 
	    _	      -> m

instance Apply Type where
    apply a []	= a
    apply (MetaT x args') args		  = MetaT x (args' ++ args)
    apply (LamT (Abs _ a)) (Arg _ v:args) = subst v a `apply` args
    apply _ _				  = __IMPOSSIBLE__

instance Apply Definition where
    apply (Defn t n d) args = Defn (apply t args) n (apply d args)

instance Apply Defn where
    apply Axiom _		     = Axiom
    apply (Function cs a) args	     = Function (apply cs args) a
    apply (Datatype np cs a) args    = Datatype (np - length args) cs a
    apply (Constructor np cs a) args = Constructor (np - length args) cs a

instance Apply Clause where
    apply (Clause ps b) args = Clause (drop (length args) ps) $ apply b args

instance Apply ClauseBody where
    apply b []				  = b
    apply (Bind (Abs _ b)) (Arg _ v:args) = subst v b `apply` args
    apply (Body _) (_:_)		  = __IMPOSSIBLE__

instance Apply t => Apply [t] where
    apply ts args = map (`apply` args) ts

-- | @(abstract args v) args --> v[args]@.
class Abstract t where
    abstract :: [Arg a] -> t -> t

instance Abstract Term where
    abstract tel v = foldl (\v _ -> Lam (Abs "x" v) []) v $ reverse tel

instance Abstract Type where
    abstract tel a = foldl (\a _ -> LamT (Abs "x" a)   ) a $ reverse tel

instance Abstract Definition where
    abstract tel (Defn t n d) = Defn (abstract tel t) n (abstract tel d)

instance Abstract Defn where
    abstract tel Axiom		       = Axiom
    abstract tel (Function cs a)       = Function (abstract tel cs) a
    abstract tel (Datatype np cs a)    = Datatype (length tel + np) cs a	-- TODO?
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

-- | Substitute @repl@ for @(Var 0 _)@ in @x@.
--
subst :: Term -> GenericT
subst repl x = runIdentity $ walk (mkM goVal) x where
  goVal (Var i args) = do
      n <- ask
      if i == n 
          then do 
              args' <- mapM goArg args	-- TODO: will this traverse more than the top-level?
              endWalk $ apply (raise n repl) args'
          else return $ Var (if i > n then i - 1 else i) args
  goVal x = return x
  
  goArg (Arg h v) = Arg h <$> goVal v

-- | Substitute a lot of terms.
substs :: [Term] -> GenericT
substs []     x = x
substs (t:ts) x = subst t (substs (raise 1 ts) x)

-- | Instantiate an abstraction
substAbs :: Data a => Term -> Abs a -> a
substAbs u (Abs _ v) = subst u v

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

