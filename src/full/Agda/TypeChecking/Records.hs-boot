
module Agda.TypeChecking.Records where

import Agda.Syntax.Internal
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common (Hiding)
import qualified Agda.Syntax.Concrete.Name as C
import Agda.TypeChecking.Monad

isRecord :: MonadTCM tcm => QName -> tcm Bool
isEtaRecord :: MonadTCM tcm => QName -> tcm Bool
getRecordFieldNames :: MonadTCM tcm => QName -> tcm [(Hiding, C.Name)]
etaContractRecord :: MonadTCM tcm => QName -> QName -> Args -> tcm Term
isGeneratedRecordConstructor :: MonadTCM tcm => QName -> tcm Bool
