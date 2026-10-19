{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Datatypes where

import Agda.TypeChecking.Monad.Signature ( HasConstInfo, SigError )
import Agda.Syntax.Internal ( QName, ConHead )
import Agda.Utils.CallStack ( HasCallStack )

getConHead         :: (HasCallStack, HasConstInfo m) => QName -> m (Either SigError ConHead)
getConstructorData :: (HasCallStack, HasConstInfo m) => QName -> m QName
