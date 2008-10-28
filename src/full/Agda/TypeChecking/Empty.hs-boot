
module Agda.TypeChecking.Empty where

import Agda.TypeChecking.Monad (MonadTCM, Constraints)
import Agda.Syntax.Internal (Type)

isEmptyType :: MonadTCM tcm => Type -> tcm ()
isEmptyTypeC :: MonadTCM tcm => Type -> tcm Constraints

