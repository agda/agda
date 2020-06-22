module Agda.TypeChecking.Primitive where

import Data.Map (Map)
import Agda.TypeChecking.Monad.Base

primitiveFunctions :: Map String (TCM PrimitiveImpl)
