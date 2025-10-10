module Agda.TypeChecking.Monad.State where

import Control.Monad.IO.Class (MonadIO)
import Agda.TypeChecking.Monad.Base (MonadFileId, TCMT)

instance MonadIO m => MonadFileId (TCMT m)
