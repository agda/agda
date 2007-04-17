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
	, emptyTypes	:: [Open Type]
	}

instance Monoid PatBindings where
    mempty = PatBinds [] [] []
    mappend (PatBinds a b e) (PatBinds c d f) =
	PatBinds (mappend a c) (mappend b d) (mappend e f)

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

runCheckPatM :: CheckPatM r a -> ([String] -> [MetaId] -> [Type] -> a -> TCM r) -> TCM r
runCheckPatM (CheckPatM m) ret = do
    flip evalStateT mempty $ runContT m $ \r -> do
	PatBinds xs metas ts <- get
	ts <- lift $ mapM getOpen ts
	lift $ ret xs metas ts r

liftPatCPS :: (forall b. (a -> TCM b) -> TCM b) -> CheckPatM r a
liftPatCPS f = CheckPatM $ ContT $ \k -> StateT $ \s -> f (\x -> runStateT (k x) s)

liftPatCPS_ :: (forall b. TCM b -> TCM b) -> CheckPatM r ()
liftPatCPS_ f = liftPatCPS (\k -> f $ k ())

bindPatternVar :: Name -> Arg Type -> CheckPatM r ()
bindPatternVar x a = do
    liftPatCPS_ (addCtx x a)
    tell (PatBinds [show x] [] [])

addPatternMeta :: MetaPriority -> Type -> CheckPatM r MetaId
addPatternMeta p a = do
    x <- newFirstOrderMeta p a
    tell (PatBinds [] [x] [])
    return x

thisTypeShouldBeEmpty :: Type -> CheckPatM r ()
thisTypeShouldBeEmpty t = do
    t <- makeOpen t
    tell (PatBinds [] [] [t])

