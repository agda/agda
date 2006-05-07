
module TypeChecking.Substitute where

import Control.Monad.Identity
import Control.Monad.Reader
import Data.Generics

import Syntax.Common
import Syntax.Internal
import Syntax.Internal.Walk

import Utils.Monad

-- | Apply something to a bunch of arguments.
apply :: Data a => a -> Args -> a
apply x args = (mkT addTrm `extT` addTyp) x
    where
	addTrm m = case m of
	    Var i args' -> Var i (args'++args)
	    Lam m args' -> Lam m (args'++args)
	    Def c args' -> Def c (args'++args)
	    Con c args' -> Con c (args'++args)
	    MetaV x args' -> MetaV x (args'++args) 
	    _	      -> m
	addTyp a = case a of
	    MetaT x args' -> MetaT x (args'++args)
	    _	      -> a

-- | @(abstract args v) args --> v[args]@.
abstract :: Data a => Args -> a -> a
abstract args = mkT absV `extT` absT where
    absV v = foldl (\v _ -> Lam  (Abs "x" v) []) v $ reverse args
    absT a = foldl (\a _ -> LamT (Abs "x" a)   ) a $ reverse args 

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

