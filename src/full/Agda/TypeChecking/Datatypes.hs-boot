
module Agda.TypeChecking.Datatypes where

import Agda.TypeChecking.Monad.Base
import Agda.Syntax.Internal

getConHead         :: QName -> TCM ConHead
getConstructorData :: QName -> TCM QName
