
module TypeChecking.MetaVars where

import Syntax.Internal	       (MetaId)
import TypeChecking.Monad.Base (MetaInstantiation, TCM)

setRef :: MetaId -> MetaInstantiation -> TCM ()

