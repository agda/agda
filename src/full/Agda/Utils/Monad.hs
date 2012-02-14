{-# LANGUAGE FlexibleContexts #-}

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
import qualified Control.Monad.State.Strict as SS
import Control.Monad.Writer
import Control.Applicative
import Data.Traversable hiding (sequence)
import Data.Foldable as Fold
import Data.Monoid

import Agda.Utils.List

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

-- | Lazy monadic conjunction.
and2M :: Monad m => m Bool -> m Bool -> m Bool
and2M ma mb = ifM ma mb (return False)

andM :: Monad m => [m Bool] -> m Bool
andM = Fold.foldl and2M (return True)

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

fmapM :: (Traversable f, Applicative m) => (a -> m b) -> f a -> m (f b)
fmapM f = commuteM . fmap f

type Cont r a = (a -> r) -> r

-- | 'Control.Monad.mapM' for the continuation monad. Terribly useful.
thread :: (a -> Cont r b) -> [a] -> Cont r [b]
thread f [] ret = ret []
thread f (x:xs) ret =
    f x $ \y -> thread f xs $ \ys -> ret (y:ys)

-- | Requires both lists to have the same lengths.
zipWithM' :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithM' f xs ys = sequence (zipWith' f xs ys)

-- | Finally for the 'Error' class. Errors in the finally part take
-- precedence over prior errors.

finally :: (Error e, MonadError e m) => m a -> m b -> m a
first `finally` after = do
  r <- catchError (liftM Right first) (return . Left)
  after
  case r of
    Left e  -> throwError e
    Right r -> return r

-- | Bracket for the 'Error' class.

bracket :: (Error e, MonadError e m)
        => m a         -- ^ Acquires resource. Run first.
        -> (a -> m c)  -- ^ Releases resource. Run last.
        -> (a -> m b)  -- ^ Computes result. Run in-between.
        -> m b
bracket acquire release compute = do
  resource <- acquire
  compute resource `finally` release resource

-- Maybe ------------------------------------------------------------------

mapMaybeM :: Applicative m => (a -> m b) -> Maybe a -> m (Maybe b)
mapMaybeM f = maybe (pure Nothing) (\x -> Just <$> f x)

-- Either -----------------------------------------------------------------

liftEither :: MonadError e m => Either e a -> m a
liftEither = either throwError return

-- Read -------------------------------------------------------------------

readM :: (Error e, MonadError e m, Read a) => String -> m a
readM s = case reads s of
	    [(x,"")]	-> return x
	    _		->
              throwError $ strMsg $ "readM: parse error string " ++ s
