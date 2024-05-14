module Agda.TypeChecking.InstanceArguments where

import Agda.TypeChecking.Monad.Base (TCM, InstanceInfo)

import Agda.Syntax.Internal (QName, Type)

addTypedInstance' :: Bool -> Maybe InstanceInfo -> QName -> Type -> TCM ()
