{-# LANGUAGE Strict, UndecidableInstances #-}

module Agda.Utils.StrictReader where

import GHC.Exts (oneShot)
import Control.Monad.Reader (MonadReader(..))
import Agda.Utils.ExpandCase

newtype ReaderT r m a = ReaderT {runReaderT :: r -> m a}

instance Monad m => Functor (ReaderT r m) where
  {-# INLINE fmap #-}
  fmap f (ReaderT ma) = ReaderT (oneShot \r -> do
    a <- ma r
    pure $! f a)
  {-# INLINE (<$) #-}
  (<$) a (ReaderT ma) = ReaderT \r -> pure a

instance Monad m => Applicative (ReaderT r m) where
  {-# INLINE pure #-}
  pure a = ReaderT (oneShot \_ -> pure a)
  {-# INLINE (<*>) #-}
  ReaderT mf <*> ReaderT ma = ReaderT (oneShot \r -> do
    f <- mf r
    a <- ma r
    pure $! f a)
  {-# INLINE (*>) #-}
  ReaderT ma *> ReaderT mb = ReaderT (oneShot \r -> do
    _ <- ma r
    mb r)
  {-# INLINE (<*) #-}
  ReaderT ma <* ReaderT mb = ReaderT (oneShot \r -> do
    a <- ma r
    _ <- mb r
    pure a)

instance Monad m => Monad (ReaderT r m) where
  {-# INLINE return #-}
  return = pure
  {-# INLINE (>>=) #-}
  ReaderT ma >>= f = ReaderT (oneShot \r -> do
    a <- ma r
    runReaderT (f a) r)
  {-# INLINE (>>) #-}
  (>>) = (*>)

instance Monad m => MonadReader r (ReaderT r m) where
  {-# INLINE ask #-}
  ask = ReaderT (oneShot \r -> pure r)
  {-# INLINE local #-}
  local f (ReaderT ma) = ReaderT (oneShot \r -> ma $! f r)
  {-# INLINE reader #-}
  reader f = ReaderT (oneShot \r -> pure $! f r)

instance (Semigroup a, Monad m) => Semigroup (ReaderT r m a) where
  {-# INLINE (<>) #-}
  ReaderT mx <> ReaderT my = ReaderT (oneShot \r -> do
    ~x <- mx r
    ~y <- my r
    pure $! x <> y)

instance (Monoid a, Monad m) => Monoid (ReaderT r m a) where
  {-# INLINE mempty #-}
  mempty = ReaderT (oneShot \r -> pure mempty)

----------------------------------------------------------------------------------------------------

newtype Reader r a = Reader {runReader :: r -> a}

instance Functor (Reader r) where
  {-# INLINE fmap #-}
  fmap f (Reader ma) = Reader (oneShot \r -> let x = ma r in f x)
  (<$) a (Reader ma) = Reader (oneShot \r -> a)

instance Applicative (Reader r) where
  {-# INLINE pure #-}
  pure a = Reader (oneShot (\_ -> a))
  {-# INLINE (<*>) #-}
  Reader mf <*> Reader ma = Reader (oneShot \r -> case mf r of f -> case ma r of a -> f a)
  {-# INLINE (*>) #-}
  Reader ma *> Reader mb = Reader (oneShot \r -> mb r)
  {-# INLINE (<*) #-}
  Reader ma <* Reader mb = Reader (oneShot \r -> ma r)

instance Monad (Reader r) where
  {-# INLINE return #-}
  return = pure
  {-# INLINE (>>=) #-}
  Reader ma >>= f = Reader (oneShot \r -> let x = ma r in runReader (f x) r)
  {-# INLINE (>>) #-}
  (>>) = (*>)

instance MonadReader r (Reader r) where
  {-# INLINE ask #-}
  ask = Reader (oneShot \r -> r)
  {-# INLINE local #-}
  local f (Reader ma) = Reader (oneShot \r -> let x = f r in ma x)
  {-# INLINE reader #-}
  reader f = Reader (oneShot \r -> f r)

instance Semigroup a => Semigroup (Reader r a) where
  {-# INLINE (<>) #-}
  Reader f <> Reader g = Reader (oneShot \r -> f r <> g r)

instance Monoid a => Monoid (Reader r a) where
  {-# INLINE mempty #-}
  mempty = Reader \_ -> mempty

instance ExpandCase a => ExpandCase (Reader r a) where
  type Result (Reader r a) = Result a
  {-# INLINE expand #-}
  expand k =
    Reader (oneShot \ ~r ->
     expand @a (oneShot \deflateA -> let r' = r in k (oneShot \act -> deflateA (runReader act r'))))
