
module Agda.TypeChecking.Datatypes where

import Agda.TypeChecking.Monad.Base
import Agda.Syntax.Internal

getConstructorData :: QName -> TCM QName
