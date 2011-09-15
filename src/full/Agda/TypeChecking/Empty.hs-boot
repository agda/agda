
module Agda.TypeChecking.Empty where

import Agda.TypeChecking.Monad (TCM)
import Agda.Syntax.Internal (Type)

isReallyEmptyType :: Type -> TCM ()
isEmptyType       :: Type -> TCM ()
