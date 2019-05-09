
module Agda.Compiler.Backend where

import Agda.Syntax.Abstract.Name (QName)
import {-# SOURCE #-} Agda.TypeChecking.Monad.Base (TCM)

data Backend

activeBackendMayEraseType :: QName -> TCM Bool
