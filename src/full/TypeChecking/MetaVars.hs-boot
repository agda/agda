
module TypeChecking.MetaVars where

import Syntax.Internal	       ( MetaId, Term )
import TypeChecking.Monad.Base ( MonadTCM )

assignTerm :: MonadTCM tcm => MetaId -> Term -> tcm ()

