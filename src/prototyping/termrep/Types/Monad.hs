{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Types.Monad where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Error

data TCState = TCState

data TCEnv = TCEnv

newtype TC a = TC { unTC :: ReaderT TCEnv (StateT TCState (ErrorT String IO)) a }
  deriving (Monad, MonadState TCState, MonadReader TCEnv, MonadError String, Functor, Applicative)
