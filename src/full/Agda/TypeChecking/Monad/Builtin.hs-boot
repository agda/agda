
module Agda.TypeChecking.Monad.Builtin where

import Control.Monad.Reader
import Control.Monad.State

import Control.Monad.IO.Class (MonadIO)

import Agda.TypeChecking.Monad.Base (TCMT, Builtin, PrimFun)

class Monad m => HasBuiltins m where
  getBuiltinThing :: String -> m (Maybe (Builtin PrimFun))

instance HasBuiltins m => HasBuiltins (ReaderT e m)
instance HasBuiltins m => HasBuiltins (StateT s m)

instance MonadIO m => HasBuiltins (TCMT m)
