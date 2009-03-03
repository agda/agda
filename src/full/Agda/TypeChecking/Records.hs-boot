
module Agda.TypeChecking.Records where

import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Concrete.Name as C
import Agda.TypeChecking.Monad

isRecord :: MonadTCM tcm => QName -> tcm Bool
getRecordFieldNames :: MonadTCM tcm => QName -> tcm [C.Name]
