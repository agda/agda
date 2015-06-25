module Agda.TypeChecking.Monad.Base where

import Control.Monad.IO.Class (MonadIO)
import Data.IORef (IORef)
import Data.Map (Map)

import Agda.Syntax.Concrete.Name (TopLevelModuleName)
import Agda.Utils.FileName (AbsolutePath)

data TCEnv
data TCState
newtype TCMT m a = TCM { unTCM :: IORef TCState -> TCEnv -> m a }

instance MonadIO m => MonadIO (TCMT m) where
instance MonadIO m => Monad (TCMT m) where

type TCM = TCMT IO

type ModuleToSource = Map TopLevelModuleName AbsolutePath
