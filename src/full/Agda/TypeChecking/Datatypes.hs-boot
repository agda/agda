{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Datatypes where

import Agda.TypeChecking.Monad.Signature
import Agda.Syntax.Internal

getConHead         :: HasConstInfo m => QName -> m (Either SigError ConHead)
getConstructorData :: HasConstInfo m => QName -> m QName
