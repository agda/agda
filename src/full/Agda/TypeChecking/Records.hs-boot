{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Records where

import Agda.Syntax.Internal
import qualified Agda.Syntax.Concrete.Name as C
import Agda.TypeChecking.Monad ( RecordData, HasConstInfo )

import Agda.Utils.CallStack ( HasCallStack )

etaContractRecord :: HasConstInfo m => QName -> ConHead -> ConInfo -> Args -> m Term

isRecord            :: (HasCallStack, HasConstInfo m) => QName -> m (Maybe RecordData)
isEtaRecord         :: (HasCallStack, HasConstInfo m) => QName -> m Bool
isRecordConstructor :: (HasCallStack, HasConstInfo m) => QName -> m (Maybe (QName, RecordData))

recordFieldNames :: RecordData -> [Dom C.Name]
