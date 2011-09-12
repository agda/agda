
module Agda.TypeChecking.Empty where

import Agda.TypeChecking.Monad (MonadTCM)
import Agda.Syntax.Internal (Type)

isReallyEmptyType :: MonadTCM tcm => Type -> tcm ()
isEmptyType       :: MonadTCM tcm => Type -> tcm ()
