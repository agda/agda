module Agda.TypeChecking.InstanceArguments where

import Agda.TypeChecking.Monad.Base (TCM)

import Agda.Syntax.Internal (QName, Type)

addTypedInstance' :: Bool -> QName -> Type -> TCM ()
