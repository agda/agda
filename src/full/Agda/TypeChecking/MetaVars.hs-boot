
module Agda.TypeChecking.MetaVars where

import Agda.Syntax.Common	    ( Arg )
import Agda.Syntax.Internal	    ( MetaId, Term, Sort, Type, Args, Abs )
import Agda.TypeChecking.Monad.Base ( TCM )

type Condition = Arg Type -> Abs Type -> Bool
newArgsMeta'      :: Condition -> Type -> TCM Args
newArgsMeta       :: Type -> TCM Args
assignTerm        :: MetaId -> Term -> TCM ()
etaExpandMetaSafe :: MetaId -> TCM ()
assignV           :: MetaId -> Args -> Term -> TCM ()
