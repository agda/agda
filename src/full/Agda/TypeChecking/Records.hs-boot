{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Records where

import Agda.Syntax.Internal
import qualified Agda.Syntax.Concrete.Name as C
import Agda.TypeChecking.Monad

isRecord :: HasConstInfo m => QName -> m (Maybe Defn)
isEtaRecord :: HasConstInfo m => QName -> m Bool
getRecordFieldNames_ :: (HasConstInfo m, ReadTCState m) => QName -> m (Maybe [Dom C.Name])
etaContractRecord :: HasConstInfo m => QName -> ConHead -> ConInfo -> Args -> m Term
isGeneratedRecordConstructor :: (MonadTCEnv m, HasConstInfo m) => QName -> m Bool
isRecordConstructor :: HasConstInfo m => QName -> m (Maybe (QName, Defn))
