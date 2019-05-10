
module Agda.TypeChecking.Monad.Builtin where

import Control.Monad.Reader
import Control.Monad.State

import qualified Control.Monad.Fail as Fail
import Control.Monad.IO.Class (MonadIO)

import Agda.TypeChecking.Monad.Base (TCMT, Builtin, PrimFun)

class ( Functor m
      , Applicative m
      , Fail.MonadFail m
      ) => HasBuiltins m where
  getBuiltinThing :: String -> m (Maybe (Builtin PrimFun))

instance HasBuiltins m => HasBuiltins (ReaderT e m)
instance HasBuiltins m => HasBuiltins (StateT s m)

instance MonadIO m => HasBuiltins (TCMT m)
