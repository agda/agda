
{-|
This is a very strict Writer monad, as a wrapper on "Agda.Utils.StrictState".
-}

module Agda.Utils.StrictWriter where

import Agda.Utils.StrictState

newtype Writer w a = Writer {unWriter :: State w a}
  deriving (Functor, Applicative, Monad)

{-# INLINE tell #-}
tell :: Monoid w => w -> Writer w ()
tell !w = Writer (modify (<> w))

{-# INLINE listen #-}
listen :: Monoid w => Writer w a -> Writer w (a, w)
listen (Writer act) = Writer do
  old <- get
  put mempty
  a <- act
  diff <- get
  put (old <> diff)
  pure (a, diff)

{-# INLINE writer #-}
writer :: Monoid w => (a, w) -> Writer w a
writer (!a, !w) = do
  tell w
  pure a

{-# INLINE censor #-}
censor :: Monoid w => (w -> w) -> Writer w a -> Writer w a
censor f (Writer act) = Writer do
  old <- get
  put mempty
  a <- act
  diff <- get
  let !diff' = f diff
  put (old <> diff')
  pure a

{-# INLINE runWriter #-}
runWriter :: Monoid w => Writer w a -> (a, w)
runWriter (Writer act) = runState act mempty

{-# INLINE execWriter #-}
execWriter :: Monoid w => Writer w a -> w
execWriter (Writer act) = execState act mempty
