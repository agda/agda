module Agda.TypeChecking.Primitive where

import Data.Map (Map)
import Agda.TypeChecking.Monad.Base
import Agda.Syntax.Builtin (PrimitiveId)

primitiveFunctions :: Map PrimitiveId (TCM PrimitiveImpl)
