
module Agda.TypeChecking.Warnings where

import Agda.TypeChecking.Monad.Base

import Agda.Utils.Except

warning :: (MonadTCM m, HasOptions m, MonadError TCErr m, ReadTCState m)
        => Warning -> m ()

warnings :: (MonadTCM m, HasOptions m, ReadTCState m, MonadError TCErr m)
         => [Warning] -> m ()
