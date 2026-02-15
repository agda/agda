
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE UnboxedTuples #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}

{-|
This is a strict state monad, where state update, monadic binding and return are all strict.  It is
specialized to the case where we have @(s, t)@ for state, i.e. two state components.  The reason for
specialization is that GHC cannot reliably unbox @State (s, t)@ for any definition of plain @State@,
so we need to directly use unboxed tuples for two state components in the internals.

If you need two strict state components and no other effects, use this module. Do not use
@Control.Monad.State.Strict@ for the same purpose; it's not even strict in state updates and is
/much/ less amenable to GHC optimizations than this module.
-}

module Agda.Utils.StrictState2 where

import GHC.Exts (oneShot)

newtype State s t a = State {runState# :: s -> t -> (# a, s, t #)}

instance Functor (State s t) where
  {-# INLINE fmap #-}
  fmap f (State g) = State (oneShot \s t -> case g s t of
    (# a, !s, !t #) -> let b = f a in (# b, s, t #))
  {-# INLINE (<$) #-}
  (<$) a m = (\_ -> a) <$> m

instance Applicative (State s t) where
  {-# INLINE pure #-}
  pure ~a = State (oneShot \s t -> (# a, s, t #))
  {-# INLINE (<*>) #-}
  State mf <*> State ma = State (oneShot \s t -> case mf s t of
    (# f, s, t #) -> case ma s t of
      (# a, !s, !t #) -> let b = f a in (# b, s, t #))
  {-# INLINE (*>) #-}
  State ma *> State mb = State (oneShot \s t -> case ma s t of
    (# _, s, t #) -> mb s t)
  {-# INLINE (<*) #-}
  State ma <* State mb = State (oneShot \s t -> case ma s t of
    (# a, s, t #) -> case mb s t of
      (# _, s, t #) -> (# a, s, t #))

instance Monad (State s t) where
  {-# INLINE return #-}
  return = pure
  {-# INLINE (>>=) #-}
  State ma >>= f = State (oneShot \s t -> case ma s t of
    (# a, s, t #) -> runState# (f a) s t)
  {-# INLINE (>>) #-}
  (>>) = (*>)

{-# INLINE put #-}
put :: s -> t -> State s t ()
put s t = State (oneShot \_ _ -> (# (), s, t #))

{-# INLINE put1 #-}
put1 :: s -> State s t ()
put1 s = State \_ t -> (# (), s, t #)

{-# INLINE put2 #-}
put2 :: t -> State s t ()
put2 t = State \s _ -> (# (), s, t #)

{-# INLINE get #-}
get :: State s t (s, t)
get = State \s t -> (# (s, t), s, t #)

{-# INLINE get1 #-}
get1 :: State s t s
get1 = State \s t -> (# s, s, t #)

{-# INLINE get2 #-}
get2 :: State s t t
get2 = State \s t -> (# t, s, t #)

{-# INLINE gets #-}
gets :: ((s, t) -> a) -> State s t a
gets f = f <$> get

{-# INLINE modify #-}
modify :: ((s,t) -> (s,t)) -> State s t ()
modify f = State \s t -> let (!s', !t') = f (s, t) in (# (), s', t' #)

{-# INLINE modify1 #-}
modify1 :: (s -> s) -> State s t ()
modify1 f = State \s t -> let !s' = f s in (# (), s', t #)

{-# INLINE modify2 #-}
modify2 :: (t -> t) -> State s t ()
modify2 f = State \s t -> let !t' = f t in (# (), s, t' #)

{-# INLINE execState #-}
execState :: State s t a -> (s, t) -> (s, t)
execState (State f) (s, t) = case f s t of
  (# _, s, t #) -> (s, t)

{-# INLINE runState #-}
runState :: State s t a -> (s, t) -> (a, (s, t))
runState (State f) (s, t) = case f s t of
  (# !a, !s, !t #) -> (a, (s, t))

{-# INLINE evalState #-}
evalState :: State s t a -> (s, t) -> a
evalState (State f) (s, t) = case f s t of
  (# a, _, _ #) -> a
