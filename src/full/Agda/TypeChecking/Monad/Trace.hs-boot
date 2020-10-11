module Agda.TypeChecking.Monad.Trace where

import Data.Kind (Type)

import Agda.Syntax.Position (HasRange)
import Agda.TypeChecking.Monad.Base (TCM)

class MonadTrace (m :: Type -> Type)
instance MonadTrace TCM

setCurrentRange :: (MonadTrace m, HasRange x) => x -> m a -> m a
