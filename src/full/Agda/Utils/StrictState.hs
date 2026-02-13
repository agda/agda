{-# LANGUAGE MagicHash, UnboxedTuples, Strict #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}

{-|
This is a plain strict state monad, where state update, monadic binding and return are all strict.
If you only need a single strict state effect, use this module.

Do not use @Control.Monad.State.Strict@ for the same purpose; it's not even strict in state updates
and is /much/ less amenable to GHC optimizations than this module.
-}

module Agda.Utils.StrictState (
    MonadState(..)
  , module Agda.Utils.StrictState
  ) where

import Control.Monad.State (MonadState(..))
import Control.Monad.Trans (MonadTrans(..))
import Data.Strict.Tuple
import GHC.Exts (oneShot)

newtype State s a = State {runState# :: s -> (# a, s #)}

instance Functor (State s) where
  {-# INLINE fmap #-}
  fmap f (State g) = State (oneShot \s -> case g s of
    (# a, !s #) -> let b = f a in (# b, s #))
  {-# INLINE (<$) #-}
  (<$) a m = (\_ -> a) <$> m

instance Applicative (State s) where
  {-# INLINE pure #-}
  pure a = State (oneShot \s -> (# a, s #))
  {-# INLINE (<*>) #-}
  State mf <*> State ma = State (oneShot \s -> case mf s of
    (# f, s #) -> case ma s of
      (# a, !s #) -> let b = f a in (# b, s #))
  {-# INLINE (*>) #-}
  State ma *> State mb = State (oneShot \s -> case ma s of
    (# _, s #) -> mb s)
  {-# INLINE (<*) #-}
  State ma <* State mb = State (oneShot \s -> case ma s of
    (# a, s #) -> case mb s of
      (# _, s #) -> (# a, s #))

instance Monad (State s) where
  {-# INLINE return #-}
  return = pure
  {-# INLINE (>>=) #-}
  State ma >>= f = State (oneShot \s -> case ma s of
    (# a, s #) -> runState# (f a) s)
  {-# INLINE (>>) #-}
  (>>) = (*>)

{-# INLINE execState #-}
execState :: State s a -> s -> s
execState (State f) s = case f s of (# _, s #) -> s

{-# INLINE runState #-}
runState :: State s a -> s -> (a, s)
runState (State f) s = case f s of (# !a, !s #) -> (a, s)

{-# INLINE evalState #-}
evalState :: State s a -> s -> a
evalState (State f) s = case f s of (# a, _ #) -> a

instance MonadState s (State s) where
  {-# INLINE state #-}
  state = \f -> State (oneShot (\s -> case f s of (!a, !s) -> (# a, s #)))
  {-# INLINE get #-}
  get = State \s -> (# s, s #)
  {-# INLINE put #-}
  put = \s -> State \_ -> (# (), s #)

{-# INLINE gets #-}
gets :: MonadState s m => (s -> a) -> m a
gets f = f <$> get

{-# INLINE modify #-}
modify :: MonadState s m => (s -> s) -> m ()
modify f = do
  s <- get
  let s' = f s
  put s'

--------------------------------------------------------------------------------

newtype StateT s m a = StateT {runStateT# :: s -> m (Pair a s)}

instance Functor m => Functor (StateT s m) where
  {-# INLINE fmap #-}
  fmap f (StateT g) = StateT (oneShot \s -> fmap (\(a :!: s) -> f a :!: s) (g s))
  {-# INLINE (<$) #-}
  (<$) a m = (\_ -> a) <$> m

-- We require Monad m in order to force strictness in the Applicative sequencing.
instance Monad m => Applicative (StateT s m) where
  {-# INLINE pure #-}
  pure a = StateT (oneShot \s -> pure (a :!: s))
  {-# INLINE (<*>) #-}
  StateT mf <*> StateT ma = StateT (oneShot \s -> do
    f :!: s <- mf s
    a :!: s <- ma s
    let b = f a
    pure (b :!: s))
  {-# INLINE (*>) #-}
  StateT ma *> StateT mb = StateT (oneShot \s -> do
     _ :!: s <- ma s
     mb s)
  {-# INLINE (<*) #-}
  StateT ma <* StateT mb = StateT (oneShot \s -> do
    a :!: s <- ma s
    _ :!: s <- mb s
    pure (a :!: s))

instance Monad m => Monad (StateT s m) where
  {-# INLINE return #-}
  return = pure
  {-# INLINE (>>=) #-}
  StateT ma >>= f = StateT (oneShot \s -> do
    a :!: s <- ma s
    runStateT# (f a) s)
  {-# INLINE (>>) #-}
  (>>) = (*>)

instance MonadTrans (StateT s) where
  {-# INLINE lift #-}
  lift ma = StateT (oneShot \s -> do a <- ma; pure (a :!: s))

instance Monad m => MonadState s (StateT s m) where
  {-# INLINE state #-}
  state = \f -> StateT (oneShot \s -> case f s of (!a, !s) -> pure (a :!: s))
  {-# INLINE get #-}
  get = StateT (\s -> pure (s :!: s))
  {-# INLINE put #-}
  put s = StateT (\_ -> pure (() :!: s))

{-# INLINE execStateT #-}
execStateT :: Monad m => StateT s m a -> s -> m s
execStateT (StateT f) s = do _ :!: s <- f s; pure s

{-# INLINE runStateT #-}
runStateT :: Monad m => StateT s m a -> s -> m (a, s)
runStateT (StateT f) s = do a :!: s <- f s; pure (a, s)

{-# INLINE evalStateT #-}
evalStateT :: Monad m => StateT s m a -> s -> m a
evalStateT (StateT f) s = do a :!: _ <- f s; pure a
