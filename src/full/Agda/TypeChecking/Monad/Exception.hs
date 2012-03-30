{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}

-- | Basically a copy of the ErrorT monad transformer. It's handy to slap
--   onto TCM and still be a MonadTCM (which isn't possible with ErrorT).

-- Andreas, 2012-03-30: the following command seems to be STALE.
--   Also, it does not require the silly Error instance for the err type.
-- The silly Error instance is back. ;-)

module Agda.TypeChecking.Monad.Exception where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Agda.TypeChecking.Monad.Base

newtype ExceptionT err m a = ExceptionT { runExceptionT :: m (Either err a) }

class Error err => MonadException err m | m -> err where
  throwException :: err -> m a
  catchException :: m a -> (err -> m a) -> m a

instance (Monad m, Error err) => Monad (ExceptionT err m) where
  return = ExceptionT . return . Right
  ExceptionT m >>= k = ExceptionT $ do
    r <- m
    case r of
      Left err -> return $ Left err
      Right x  -> runExceptionT $ k x
  fail = ExceptionT . return . Left . strMsg

instance (Monad m, Error err) => MonadException err (ExceptionT err m) where
  throwException = ExceptionT . return . Left
  catchException m h = ExceptionT $ do
    r <- runExceptionT m
    case r of
      Left err  -> runExceptionT $ h err
      Right x   -> return $ Right x

instance (Monad m, MonadException err m) => MonadException err (ReaderT r m) where
  throwException = lift . throwException
  catchException m h = ReaderT $ \ r ->
    catchException (m `runReaderT` r) (\ err -> h err `runReaderT` r)

instance (Monad m, MonadException err m, Monoid w) => MonadException err (WriterT w m) where
  throwException = lift . throwException
  catchException m h = WriterT $
    catchException (runWriterT m) (\ err -> runWriterT $ h err)

instance MonadTrans (ExceptionT err) where
  lift = ExceptionT . liftM Right

instance Functor f => Functor (ExceptionT err f) where
  fmap f = ExceptionT . fmap (either Left (Right . f)) . runExceptionT

instance (Error err, Applicative m, Monad m) => Applicative (ExceptionT err m) where
  pure  = return
  (<*>) = ap

instance (Error err, MonadState s m) => MonadState s (ExceptionT err m) where
  get   = ExceptionT $ Right `liftM` get
  put x = ExceptionT $ Right `liftM` put x

instance (Error err, MonadReader r m) => MonadReader r (ExceptionT err m) where
  ask     = ExceptionT $ Right `liftM` ask
  local f = ExceptionT . local f . runExceptionT

instance (Error err, MonadError err' m) => MonadError err' (ExceptionT err m) where
  throwError err = ExceptionT $ Right `liftM` throwError err
  catchError m h = ExceptionT $ runExceptionT m `catchError` (runExceptionT . h)

instance (Error err, MonadIO m) => MonadIO (ExceptionT err m) where
  liftIO m = ExceptionT $ Right `liftM` liftIO m

instance (Error err, MonadTCM tcm) => MonadTCM (ExceptionT err tcm) where
  liftTCM m = ExceptionT $ Right `liftM` liftTCM m
