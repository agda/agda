{-# OPTIONS_GHC -fglasgow-exts #-}

module TypeChecking.Patterns.Monad where

import Control.Applicative
import Control.Monad.Cont
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error
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

newtype CheckPatM r a = CheckPatM { unCheckPatM :: ContT r (StateT PatBindings TCM) a }
    deriving (Functor, Monad, MonadReader TCEnv, MonadIO)

instance Applicative (CheckPatM r) where
    pure  = return
    (<*>) = ap

instance MonadState TCState (CheckPatM r) where
    get = liftTCM get
    put = liftTCM . put

instance MonadTCM (CheckPatM r) where
    liftTCM = CheckPatM . lift . lift

tell :: PatBindings -> CheckPatM r ()
tell p = CheckPatM $ modify (`mappend` p)

runCheckPatM :: CheckPatM r a -> ([String] -> [MetaId] -> a -> TCM r) -> TCM r
runCheckPatM (CheckPatM m) ret = do
    flip evalStateT mempty $ runContT m $ \r -> do
	PatBinds xs metas <- get
	lift $ ret xs metas r

liftPatCPS :: (forall b. (a -> TCM b) -> TCM b) -> CheckPatM r a
liftPatCPS f = CheckPatM $ ContT $ \k -> StateT $ \s -> f (\x -> runStateT (k x) s)

liftPatCPS_ :: (forall b. TCM b -> TCM b) -> CheckPatM r ()
liftPatCPS_ f = liftPatCPS (\k -> f $ k ())

bindPatternVar :: Name -> Type -> CheckPatM r ()
bindPatternVar x a = do
    liftPatCPS_ (addCtx x a)
    tell (PatBinds [show x] [])

addPatternMeta :: Type -> CheckPatM r MetaId
addPatternMeta a = do
    x <- newFirstOrderMeta a
    tell (PatBinds [] [x])
    return x


