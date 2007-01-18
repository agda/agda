
module TypeChecking.Monad.Context where

import TypeChecking.Monad.Base

getContext :: MonadTCM tcm => tcm Context

