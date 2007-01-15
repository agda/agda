{-# OPTIONS_GHC -fglasgow-exts #-}

module TypeChecking.Patterns.Monad where

import Control.Monad.Cont
import Control.Monad.State
import Data.Monoid

import Syntax.Common
import Syntax.Internal

import TypeChecking.Monad
import TypeChecking.Substitute
import TypeChecking.MetaVars

data PatBindings = PatBinds
	{ boundNames	:: [String]
	, metaVariables :: [MetaId]
	}

instance Monoid PatBindings where
    mempty = PatBinds [] []
    mappend (PatBinds a b) (PatBinds c d) = PatBinds (mappend a c) (mappend b d)

type CheckPatM r = ContT r (StateT PatBindings TCM)

tell :: PatBindings -> CheckPatM r ()
tell p = modify (`mappend` p)

runCheckPatM :: CheckPatM r a -> ([String] -> [MetaId] -> a -> TCM r) -> TCM r
runCheckPatM m ret = do
    flip evalStateT mempty $ runContT m $ \r -> do
	PatBinds xs metas <- get
	lift $ ret xs metas r

liftPat :: TCM a -> CheckPatM r a
liftPat = lift . lift

liftPatCPS :: (forall b. (a -> TCM b) -> TCM b) -> CheckPatM r a
liftPatCPS f = ContT $ \k -> StateT $ \s -> f (\x -> runStateT (k x) s)

liftPatCPS_ :: (forall b. TCM b -> TCM b) -> CheckPatM r ()
liftPatCPS_ f = liftPatCPS (\k -> f $ k ())

bindPatternVar :: Name -> Type -> CheckPatM r ()
bindPatternVar x a = do
    liftPatCPS_ (addCtx x a)
    tell (PatBinds [show x] [])

addPatternMeta :: Type -> CheckPatM r MetaId
addPatternMeta a = do
    x <- liftPat $ newFirstOrderMeta a
    tell (PatBinds [] [x])
    return x


