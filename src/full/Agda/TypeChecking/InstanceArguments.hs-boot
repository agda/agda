module Agda.TypeChecking.InstanceArguments where

import Agda.TypeChecking.Monad.Base (TCM, InstanceInfo)

import Agda.Syntax.Common (KwRange)
import Agda.Syntax.Internal (QName, Type)

addTypedInstance' :: Bool -> Bool -> Maybe InstanceInfo -> KwRange -> QName -> Type -> TCM ()
