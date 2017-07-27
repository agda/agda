module Agda.TypeChecking.Monad.Debug where

import Control.Applicative
import Control.Monad.IO.Class (MonadIO)

import Agda.TypeChecking.Monad.Base
import {-# SOURCE #-} Agda.TypeChecking.Monad.Options

import Agda.Utils.Pretty

class (Functor m, Applicative m, Monad m) => MonadDebug m where
  displayDebugMessage :: Int -> String -> m ()
  displayDebugMessage n s = traceDebugMessage n s $ return ()

  traceDebugMessage :: Int -> String -> m a -> m a
  traceDebugMessage n s cont = displayDebugMessage n s >> cont

  formatDebugMessage  :: VerboseKey -> Int -> TCM Doc -> m String

instance (MonadIO m) => MonadDebug (TCMT m)

reportS :: (HasOptions m, MonadDebug m)
        => VerboseKey -> Int -> String -> m ()
reportSLn :: (HasOptions m, MonadDebug m)
          => VerboseKey -> Int -> String -> m ()
reportSDoc :: (HasOptions m, MonadDebug m)
           => VerboseKey -> Int -> TCM Doc -> m ()

