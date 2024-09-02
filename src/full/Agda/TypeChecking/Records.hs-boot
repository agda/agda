{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Records where

import Agda.Syntax.Internal
import qualified Agda.Syntax.Concrete.Name as C
import Agda.TypeChecking.Monad

etaContractRecord :: HasConstInfo m => QName -> ConHead -> ConInfo -> Args -> m Term

isRecord :: HasConstInfo m => QName -> m (Maybe RecordData)
isEtaRecord :: HasConstInfo m => QName -> m Bool
isRecordConstructor :: HasConstInfo m => QName -> m (Maybe (QName, RecordData))

recordFieldNames :: RecordData -> [Dom C.Name]
