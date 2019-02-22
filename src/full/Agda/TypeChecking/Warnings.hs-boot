
module Agda.TypeChecking.Warnings where

import Agda.TypeChecking.Monad.Base

import Agda.Utils.Except

class (MonadPretty m, MonadError TCErr m) => MonadWarning m where
  addWarning :: TCWarning -> m ()

warnings :: MonadWarning m => [Warning] -> m ()

warning :: MonadWarning m => Warning -> m ()
