
{-| State-based implementation of a strict writer monad. Control.Monad.Trans.Writer.CPS is similar,
    but it a) doesn't export its constructor b) is not as strict c) has no ControlMonadTrans instance.
    Hence the current module.

    NOTE: this implementation, like Writer.CPS, appends the new elements to the
    right the state. Hence, `tell`-ing lists iteratively is quadratic! Use DList-s
    instead in those cases.
  -}

module Agda.Utils.Writer (
    module Control.Monad.Writer.Class
  , WriterT(..)
  , Writer
  , runWriter
  , execWriter
  , mapWriter
  , writerT
  , runWriterT
  , execWriterT
  , mapWriterT
  ) where

import Control.Applicative
import Control.Monad
import Control.Monad.Fix
import Control.Monad.IO.Class
import Control.Monad.Signatures
import Control.Monad.Trans.Class
import Control.Monad.Trans.Control
import Control.Monad.Writer.Class
import Data.Functor.Identity
import Data.Monoid
import qualified Control.Monad.Fail as Fail

-- ---------------------------------------------------------------------------
-- | A writer monad parameterized by the type @w@ of output to accumulate.
--
-- The 'return' function produces the output 'mempty', while '>>='
-- combines the outputs of the subcomputations using 'mappend'.
type Writer w = WriterT w Identity

-- | Unwrap a writer computation as a (result, output) pair.
-- (The inverse of 'writer'.)
runWriter :: (Monoid w) => Writer w a -> (a, w)
runWriter = runIdentity . runWriterT
{-# INLINE runWriter #-}

-- | Extract the output from a writer computation.
--
-- * @'execWriter' m = 'snd' ('runWriter' m)@
execWriter :: (Monoid w) => Writer w a -> w
execWriter = runIdentity . execWriterT
{-# INLINE execWriter #-}

-- | Map both the return value and output of a computation using
-- the given function.
--
-- * @'runWriter' ('mapWriter' f m) = f ('runWriter' m)@
mapWriter :: (Monoid w, Monoid w') =>
    ((a, w) -> (b, w')) -> Writer w a -> Writer w' b
mapWriter f = mapWriterT (Identity . f . runIdentity)
{-# INLINE mapWriter #-}

-- ---------------------------------------------------------------------------
-- | A writer monad parameterized by:
--
--   * @w@ - the output to accumulate.
--
--   * @m@ - The inner monad.
--
-- The 'return' function produces the output 'mempty', while '>>='
-- combines the outputs of the subcomputations using 'mappend'.

newtype WriterT w m a = WriterT { unWriterT :: w -> m (a, w) }

-- | Construct a writer computation from a (result, output) computation.
-- (The inverse of 'runWriterT'.)
writerT :: (Functor m, Monoid w) => m (a, w) -> WriterT w m a
writerT f = WriterT $ \w -> (\(a, w') -> let !wt = w `mappend` w' in (a, wt)) <$> f
{-# INLINE writerT #-}

-- | Unwrap a writer computation.
-- (The inverse of 'writerT'.)
runWriterT :: (Monoid w) => WriterT w m a -> m (a, w)
runWriterT m = unWriterT m mempty
{-# INLINE runWriterT #-}

-- | Extract the output from a writer computation.
--
-- * @'execWriterT' m = 'liftM' 'snd' ('runWriterT' m)@
execWriterT :: (Monad m, Monoid w) => WriterT w m a -> m w
execWriterT m = do
    (!_, !w) <- runWriterT m
    return w
{-# INLINE execWriterT #-}

-- | Map both the return value and output of a computation using
-- the given function.
--
-- * @'runWriterT' ('mapWriterT' f m) = f ('runWriterT' m)@
mapWriterT :: (Monad n, Monoid w, Monoid w') =>
    (m (a, w) -> n (b, w')) -> WriterT w m a -> WriterT w' n b
mapWriterT f m = WriterT $ \ w -> do
    (!a, !w') <- f (runWriterT m)
    let !wt = w `mappend` w'
    return (a, wt)
{-# INLINE mapWriterT #-}

instance (Functor m) => Functor (WriterT w m) where
    fmap f m = WriterT $ \w -> (\(a, w') -> (f a, w')) <$> unWriterT m w
    {-# INLINE fmap #-}

instance (Functor m, Monad m) => Applicative (WriterT w m) where
    pure a = WriterT $ \w -> return (a, w)
    {-# INLINE pure #-}

    WriterT mf <*> WriterT mx = WriterT $ \ w -> do
        (!f, !w') <- mf w
        (!x, !w'') <- mx w'
        let !res = f x
        return (res, w'')
    {-# INLINE (<*>) #-}

instance (Functor m, MonadPlus m) => Alternative (WriterT w m) where
    empty = WriterT $ \_ -> mzero
    {-# INLINE empty #-}

    WriterT m <|> WriterT n = WriterT $ \w -> m w `mplus` n w
    {-# INLINE (<|>) #-}

instance (Monad m) => Monad (WriterT w m) where
    m >>= k = WriterT $ \ w -> do
        (!a, !w') <- unWriterT m w
        unWriterT (k a) w'
    {-# INLINE (>>=) #-}

instance (Functor m, MonadPlus m) => MonadPlus (WriterT w m) where
    mzero = empty
    {-# INLINE mzero #-}
    mplus = (<|>)
    {-# INLINE mplus #-}

instance MonadTrans (WriterT w) where
    lift m = WriterT $ \ w -> do
        a <- m
        return (a, w)
    {-# INLINE lift #-}

instance (MonadIO m) => MonadIO (WriterT w m) where
    liftIO = lift . liftIO
    {-# INLINE liftIO #-}

instance MonadTransControl (WriterT w) where
  type StT (WriterT w) a = (a, w)
  liftWith f = WriterT (\s -> liftM (\x -> (x, s)) (f (\t -> unWriterT t s)))
  restoreT x = WriterT (\_ -> x)
  {-# INLINE liftWith #-}
  {-# INLINE restoreT #-}

instance (Fail.MonadFail m) => Fail.MonadFail (WriterT w m) where
    fail msg = WriterT $ \_ -> Fail.fail msg
    {-# INLINE fail #-}

instance (Monoid w, Monad m) => MonadWriter w (WriterT w m) where
    writer (!a, !w') =
      WriterT (\w -> let !wt = w `mappend` w' in return (a, wt))
    tell !w =
      writer ((), w)
    listen !m = WriterT $ \w -> do
      (!a, !w') <- runWriterT m
      let !wt  = w `mappend` w'
      return ((a, w'), wt)
    pass !m = WriterT $ \w -> do
      ((!a, !f), !w') <- runWriterT m
      let !wt = w `mappend` f w'
      return (a, wt)
    {-# INLINE writer #-}
    {-# INLINE tell #-}
    {-# INLINE listen #-}
    {-# INLINE pass #-}
