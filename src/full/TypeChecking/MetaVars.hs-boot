
module TypeChecking.MetaVars where

import Syntax.Internal	       ( MetaId, Term )
import TypeChecking.Monad.Base ( TCM )

assignTerm :: MetaId -> Term -> TCM ()

