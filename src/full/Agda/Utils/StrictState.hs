{-# LANGUAGE MagicHash, UnboxedTuples, Strict #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}

{-|
This is a plain strict state monad, where state update, monadic binding and return are all strict.
If you only need a single strict state effect, use this module.

Do not use @Control.Monad.State.Strict@ for the same purpose; it's not even strict in state updates
and is /much/ less amenable to GHC optimizations than this module.
-}

module Agda.Utils.StrictState where

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

{-# INLINE put #-}
put :: s -> State s ()
put s = State \_ -> (# (), s #)

{-# INLINE get #-}
get :: State s s
get = State \s -> (# s, s #)

{-# INLINE gets #-}
gets :: (s -> a) -> State s a
gets f = f <$> get

{-# INLINE modify #-}
modify :: (s -> s) -> State s ()
modify f = State \s -> let s' = f s in (# (), s' #)

{-# INLINE execState #-}
execState :: State s a -> s -> s
execState (State f) s = case f s of
  (# _, s #) -> s

{-# INLINE runState #-}
runState :: State s a -> s -> (a, s)
runState (State f) s = case f s of
  (# !a, !s #) -> (a, s)

{-# INLINE evalState #-}
evalState :: State s a -> s -> a
evalState (State f) s = case f s of
  (# a, _ #) -> a
