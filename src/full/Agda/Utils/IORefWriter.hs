{-# LANGUAGE UndecidableInstances #-} -- For MonadTransControl
-- | Writer monad transformer based on IORefs.
module Agda.Utils.IORefWriter
  ( IORefWriterT
  , runIORefWriterT
  ) where

import Data.IORef
import Control.Monad.Trans.Control
import Control.Monad.Trans
import Control.Monad.Reader
import Control.Monad.Writer

newtype IORefWriterT w m a = IORefWriterT { unIORefWriterT :: ReaderT (IORef w) m a }
  deriving (Functor, Applicative, Monad, MonadTrans, MonadTransControl, MonadIO)

runIORefWriterT :: (MonadIO m, Monoid w) => IORefWriterT w m a -> m (a, w)
runIORefWriterT (IORefWriterT m) = do
  r <- liftIO $ newIORef mempty
  x <- runReaderT m r
  w <- liftIO $ readIORef r
  pure (x, w)

mapIORefWriterT :: (MonadIO m, Monoid w', Monoid w) => (w -> w') -> IORefWriterT w m a -> IORefWriterT w' m a
mapIORefWriterT f m = do
  (x, w') <- lift $ runIORefWriterT m
  tell (f w')
  pure x

instance (MonadIO m, Monoid w) => MonadWriter w (IORefWriterT w m) where
  tell w = writeOut . (<> w) =<< readOut

  listen m = do
    w <- readOut
    writeOut mempty
    x <- m
    w' <- readOut
    writeOut (w <> w')
    pure (x, w')

  pass m = do
    w <- readOut
    writeOut mempty
    (x, f) <- m
    w' <- readOut
    writeOut (w <> f w')
    pure x

-- Do not export!
readOut :: MonadIO m => IORefWriterT w m w
readOut = IORefWriterT $ ask >>= \ r -> liftIO (readIORef r)

-- Do not export!
writeOut :: MonadIO m => w -> IORefWriterT w m ()
writeOut w = IORefWriterT $ ask >>= \ r -> liftIO (writeIORef r w)

