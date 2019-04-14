
module Agda.TypeChecking.Empty where

import Agda.TypeChecking.Monad (TCM)
import Agda.Syntax.Internal (Type, Telescope)
import Agda.Syntax.Position (Range)

data ErrorNonEmpty

isEmptyType :: Type      -> TCM Bool
isEmptyTel  :: Telescope -> TCM Bool

ensureEmptyType :: Range -> Type -> TCM ()
checkEmptyTel   :: Range -> Telescope -> TCM (Either ErrorNonEmpty Int)
