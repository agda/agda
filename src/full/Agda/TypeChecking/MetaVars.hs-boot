
module Agda.TypeChecking.MetaVars where

import Agda.Syntax.Internal	       ( MetaId, Term )
import Agda.TypeChecking.Monad.Base ( MonadTCM )

assignTerm :: MonadTCM tcm => MetaId -> Term -> tcm ()

