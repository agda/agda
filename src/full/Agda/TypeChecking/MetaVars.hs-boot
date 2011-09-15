
module Agda.TypeChecking.MetaVars where

import Agda.Syntax.Internal	    ( MetaId, Term, Sort, Type, Args )
import Agda.TypeChecking.Monad.Base ( TCM )

assignTerm        :: MetaId -> Term -> TCM ()
etaExpandMetaSafe :: MetaId -> TCM ()
assignV           :: MetaId -> Args -> Term -> TCM ()
