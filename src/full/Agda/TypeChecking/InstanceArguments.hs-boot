
module Agda.TypeChecking.InstanceArguments where

import Agda.TypeChecking.Monad.Base (TCM)
import Agda.Syntax.Internal (Type, Term)

initializeIFSMeta :: Type -> TCM Term
