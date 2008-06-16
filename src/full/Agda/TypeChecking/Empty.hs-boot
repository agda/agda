
module Agda.TypeChecking.Empty where

import Agda.TypeChecking.Monad (MonadTCM)
import Agda.Syntax.Internal (Type)

isEmptyType :: MonadTCM tcm => Type -> tcm ()

