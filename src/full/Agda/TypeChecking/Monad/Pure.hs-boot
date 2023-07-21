{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Monad.Pure where

import Control.Monad.Reader ( ReaderT )
import Control.Monad.State ( StateT )
import Control.Monad.Trans.Identity ( IdentityT )
import Control.Monad.Writer ( WriterT )

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Builtin
import {-# SOURCE #-} Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import {-# SOURCE #-} Agda.TypeChecking.Monad.Signature

class
  ( HasBuiltins m
  , HasConstInfo m
  , MonadAddContext m
  , MonadDebug m
  , MonadReduce m
  , MonadTCEnv m
  , ReadTCState m
  ) => PureTCM m where

instance PureTCM TCM where
instance PureTCM m => PureTCM (IdentityT m)
instance PureTCM m => PureTCM (ReaderT r m)
instance (PureTCM m, Monoid w) => PureTCM (WriterT w m)
instance PureTCM m => PureTCM (StateT s m)
