
module Agda.TypeChecking.Empty where

import Agda.TypeChecking.Monad (TCM)
import Agda.Syntax.Internal (Type, Telescope)
import Agda.Syntax.Position (Range)

-- isReallyEmptyType :: Type -> TCM ()
isEmptyType       :: Range -> Type -> TCM ()
isEmptyTel        :: Telescope -> TCM Bool
