{-# OPTIONS_GHC -Wunused-imports #-}

-- | A typeclass collecting all 'pure' typechecking operations
-- | (i.e. ones that do not modify the typechecking state, throw or
-- | catch errors, or do IO other than debug printing).


module Agda.TypeChecking.Monad.Pure where

import Control.Monad.Except ( ExceptT )
import Control.Monad.Trans.Maybe ( MaybeT )
import Control.Monad.Reader ( ReaderT )
import Control.Monad.State ( StateT )
import Control.Monad.Trans.Identity ( IdentityT )
import Control.Monad.Writer ( WriterT )

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Monad.Context
import Agda.TypeChecking.Monad.Debug
import Agda.TypeChecking.Monad.Signature

import Agda.Utils.ListT
import Agda.Utils.Update

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
instance PureTCM m => PureTCM (BlockT m)
instance PureTCM m => PureTCM (ChangeT m)
instance PureTCM m => PureTCM (ExceptT e m)
instance PureTCM m => PureTCM (IdentityT m)
instance PureTCM m => PureTCM (ListT m)
instance PureTCM m => PureTCM (MaybeT m)
instance PureTCM m => PureTCM (ReaderT r m)
instance (PureTCM m, Monoid w) => PureTCM (WriterT w m)
instance PureTCM m => PureTCM (StateT s m)
