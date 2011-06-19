
module Agda.TypeChecking.MetaVars where

import Agda.Syntax.Internal	       ( MetaId, Term, Sort, Type, Args )
import Agda.TypeChecking.Monad.Base ( MonadTCM, Constraints )

assignTerm :: MonadTCM tcm => MetaId -> Term -> tcm ()

etaExpandMetaSafe :: MonadTCM tcm => MetaId -> tcm ()

assignV :: MonadTCM tcm => MetaId -> Args -> Term -> tcm Constraints
