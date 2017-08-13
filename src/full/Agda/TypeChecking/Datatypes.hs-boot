
module Agda.TypeChecking.Datatypes where

import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Signature
import Agda.Syntax.Internal

getConHead         :: QName -> TCM (Either SigError ConHead)
getConstructorData :: HasConstInfo m => QName -> m QName
