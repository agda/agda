{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Builtin where

#if __GLASGOW_HASKELL__ >= 800
import qualified Control.Monad.Fail as Fail
#endif
import Control.Monad.IO.Class (MonadIO)

import Agda.TypeChecking.Monad.Base (TCMT, Builtin, PrimFun)

class ( Functor m
      , Applicative m
#if __GLASGOW_HASKELL__ == 710
      , Monad m
#else
      , Fail.MonadFail m
#endif
      ) => HasBuiltins m where
  getBuiltinThing :: String -> m (Maybe (Builtin PrimFun))

instance MonadIO m => HasBuiltins (TCMT m)
