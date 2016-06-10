
module Agda.TypeChecking.Monad.Signature where

import Agda.Syntax.Internal (ModuleName, Telescope)
import Agda.TypeChecking.Monad.Base (TCM, ReadTCState)

inFreshModuleIfFreeParams :: TCM a -> TCM a
lookupSection :: (Functor m, ReadTCState m) => ModuleName -> m Telescope

