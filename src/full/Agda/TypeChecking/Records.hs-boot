
module Agda.TypeChecking.Records where

import Agda.Syntax.Internal
import Agda.Syntax.Abstract.Name
import qualified Agda.Syntax.Concrete.Name as C
import Agda.TypeChecking.Monad

isRecord :: QName -> TCM (Maybe Defn)
isEtaRecord :: QName -> TCM Bool
getRecordFieldNames :: QName -> TCM [Arg C.Name]
etaContractRecord :: QName -> QName -> Args -> TCM Term
isGeneratedRecordConstructor :: QName -> TCM Bool
