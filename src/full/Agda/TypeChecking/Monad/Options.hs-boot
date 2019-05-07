module Agda.TypeChecking.Monad.Options where

import Control.Monad.Reader

import Agda.TypeChecking.Monad.Base
import Agda.Utils.FileName

getIncludeDirs :: HasOptions m => m [AbsolutePath]

type VerboseKey = String

hasVerbosity :: HasOptions m => VerboseKey -> Int -> m Bool
verboseS :: (MonadTCEnv m, HasOptions m) => VerboseKey -> Int -> m () -> m ()

enableCaching :: HasOptions m => m Bool
