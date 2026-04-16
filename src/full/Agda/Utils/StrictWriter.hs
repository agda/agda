{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-bang-patterns #-}
{-|
This is a very strict Writer monad, as a wrapper on "Agda.Utils.StrictState".
-}

module Agda.Utils.StrictWriter (
    MonadWriter(..)
  , censor
  , module Agda.Utils.StrictWriter )
  where

import Control.Monad.Reader (MonadReader(..))
import Control.Monad.Except (MonadError(..))
import Control.Monad.State (MonadState(..))
import Control.Monad.Trans (MonadTrans(..))
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Trans.Control (MonadTransControl(..))
import Control.Monad.Writer (MonadWriter(..), censor)
import Data.Strict.Tuple
import GHC.Exts (oneShot)
import Agda.Utils.StrictState
import Agda.Utils.ExpandCase

newtype Writer w a = Writer {unWriter :: State w a}
  deriving (Functor, Applicative, Monad)

deriving instance ExpandCase (State w a) => ExpandCase (Writer w a)

{-# INLINE runWriter #-}
runWriter :: Monoid w => Writer w a -> (a, w)
runWriter (Writer act) = runState act mempty

{-# INLINE execWriter #-}
execWriter :: Monoid w => Writer w a -> w
execWriter (Writer act) = execState act mempty

instance Monoid w => MonadWriter w (Writer w) where
  {-# INLINE tell #-}
  tell w = Writer (modify (<> w))

  pass (Writer (State m)) = Writer (State (oneShot \w -> case m w of
    (# (!a, !f), w' #) -> let wt = w <> f w' in (# a, wt #)))

  {-# INLINE listen #-}
  listen (Writer act) = Writer do
    old <- get
    put mempty
    a <- act
    diff <- get
    put (old <> diff)
    pure (a, diff)

  {-# INLINE writer #-}
  writer (!a, !w) = do
    tell w
    pure a

newtype WriterT w m a = WriterT {unWriterT :: StateT w m a}
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO, MonadTransControl)

deriving instance ExpandCase (m (Pair a w)) => ExpandCase (WriterT w m a)
deriving instance (Monad m, MonadError e (StateT w m)) => MonadError e (WriterT w m)
deriving instance (Monad m, MonadReader r (StateT w m)) => MonadReader r (WriterT w m)
deriving instance (Monad m, MonadState s (StateT w m)) => MonadState s (WriterT w m)


instance (Monoid w, Monad m) => MonadWriter w (WriterT w m) where
  {-# INLINE tell #-}
  tell w = WriterT (modify (<> w))

  {-# INLINE pass #-}
  pass (WriterT (StateT m)) = WriterT (StateT (oneShot \w -> do
    (!a, !f) :!: w' <- m w
    let wt = w <> f w'
    pure (a :!: wt)))

  {-# INLINE listen #-}
  listen (WriterT act) = WriterT do
    old <- get
    put mempty
    a <- act
    diff <- get
    put (old <> diff)
    pure (a, diff)

  {-# INLINE writer #-}
  writer (!a, !w) = do
    tell w
    pure a

{-# INLINE runWriterT #-}
runWriterT :: Monoid w => Monad m => WriterT w m a -> m (a, w)
runWriterT (WriterT act) = runStateT act mempty

{-# INLINE execWriterT #-}
execWriterT :: Monoid w => Monad m => WriterT w m a -> m w
execWriterT (WriterT act) = execStateT act mempty
