module Agda.TypeChecking.Monad.State where

import Control.Monad.IO.Class (MonadIO)
import Control.Monad.Catch
import Agda.TypeChecking.Monad.Base (MonadFileId, TCMT)

instance (MonadIO m, MonadMask m) => MonadFileId (TCMT m)
