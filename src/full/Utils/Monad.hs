
module Utils.Monad
    ( module Utils.Monad
    , module Control.Monad
    , module Data.FunctorM
    ) where

import Control.Monad
import Data.FunctorM

-- Monads -----------------------------------------------------------------

infixl 8 <$>,<*>,<.>

(<$>) :: Monad m => (a -> b) -> m a -> m b
(<$>) = liftM

(<*>) :: Monad m => m (a -> b) -> m a -> m b
(<*>) = ap

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

forgetM :: Monad m => m a -> m ()
forgetM m = const () <$> m

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = concat <$> mapM f xs

-- | Depending on the monad you have to look at the result for
--   the force to be effective. For the 'IO' monad you do.
force :: Monad m => [a] -> m ()
force xs = do () <- length xs `seq` return ()
	      return ()

commuteM :: (FunctorM f, Monad m) => f (m a) -> m (f a)
commuteM = fmapM id

-- Maybe ------------------------------------------------------------------

mapMaybeM :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
mapMaybeM f = maybe (return Nothing) (\x -> Just <$> f x)

-- Read -------------------------------------------------------------------

readM :: (Monad m, Read a) => String -> m a
readM s = case reads s of
	    [(x,"")]	-> return x
	    _		-> fail $ "readM: parse error string " ++ s

