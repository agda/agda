{-# LANGUAGE CPP #-}

module Agda.Utils.Monad
    ( module Agda.Utils.Monad
    , (<$>), (<*>)
    )
    where

import Prelude		   hiding (concat)
import Control.Monad
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Applicative
import Data.Traversable
import Data.Foldable
import Data.Monoid

#include "../undefined.h"
import Agda.Utils.Impossible

-- Instances --------------------------------------------------------------

instance Applicative (Reader env) where
  pure  = return
  (<*>) = ap

instance Monad m => Applicative (ReaderT env m) where
  pure  = return
  (<*>) = ap

instance Monad m => Applicative (StateT s m) where
  pure  = return
  (<*>) = ap

instance (Monoid o, Monad m) => Applicative (WriterT o m) where
  pure	= return
  (<*>)	= ap

instance Applicative (State s) where
  pure	= return
  (<*>)	= ap

-- Monads -----------------------------------------------------------------

infixl 8 <.>

(<.>) :: Monad m => (b -> m c) -> (a -> m b) -> a -> m c
f <.> g = \x -> f =<< g x

whenM :: Monad m => m Bool -> m () -> m ()
whenM c m = do	b <- c
		when b m

unlessM :: Monad m => m Bool -> m () -> m ()
unlessM c m = do    b <- c
		    unless b m

ifM :: Monad m => m Bool -> m a -> m a -> m a
ifM c m m' =
    do	b <- c
	if b then m else m'

forgetM :: Applicative m => m a -> m ()
forgetM m = const () <$> m

concatMapM :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = concat <$> traverse f xs

-- | Depending on the monad you have to look at the result for
--   the force to be effective. For the 'IO' monad you do.
forceM :: Monad m => [a] -> m ()
forceM xs = do () <- length xs `seq` return ()
	       return ()

commuteM :: (Traversable f, Applicative m) => f (m a) -> m (f a)
commuteM = traverse id

type Cont r a = (a -> r) -> r

-- | 'Control.Monad.mapM' for the continuation monad. Terribly useful.
thread :: (a -> Cont r b) -> [a] -> Cont r [b]
thread f [] ret = ret []
thread f (x:xs) ret =
    f x $ \y -> thread f xs $ \ys -> ret (y:ys)

-- | Requires both lists to have the same lengths.
zipWithM' :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithM' f []	     []	      = return []
zipWithM' f (x : xs) (y : ys) = liftM2 (:) (f x y) (zipWithM' f xs ys)
zipWithM' f []	     (_ : _)  = {- ' -} __IMPOSSIBLE__
zipWithM' f (_ : _)  []	      = {- ' -} __IMPOSSIBLE__

-- Maybe ------------------------------------------------------------------

mapMaybeM :: Applicative m => (a -> m b) -> Maybe a -> m (Maybe b)
mapMaybeM f = maybe (pure Nothing) (\x -> Just <$> f x)

-- Either -----------------------------------------------------------------

liftEither :: MonadError e m => Either e a -> m a
liftEither = either throwError return

-- Read -------------------------------------------------------------------

readM :: (Monad m, Read a) => String -> m a
readM s = case reads s of
	    [(x,"")]	-> return x
	    _		-> fail $ "readM: parse error string " ++ s

