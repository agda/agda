
module Agda.TypeChecking.Empty where

import Agda.TypeChecking.Monad (TCM)
import Agda.Syntax.Internal (Type)
import Agda.Syntax.Position (Range)

-- isReallyEmptyType :: Type -> TCM ()
isEmptyType       :: Range -> Type -> TCM ()
