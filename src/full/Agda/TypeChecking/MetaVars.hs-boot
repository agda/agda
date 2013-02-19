
module Agda.TypeChecking.MetaVars where

import Agda.Syntax.Internal	    ( MetaId, Term, Sort, Type, Args, Abs, Dom )
import Agda.TypeChecking.Monad.Base ( TCM, RunMetaOccursCheck(..) )

type Condition = Dom Type -> Abs Type -> Bool
newArgsMeta'      :: Condition -> Type -> TCM Args
newArgsMeta       :: Type -> TCM Args
assignTerm        :: MetaId -> Term -> TCM ()
etaExpandMetaSafe :: MetaId -> TCM ()
assignV           :: MetaId -> Args -> Term -> TCM ()
assign 		  :: MetaId -> Args -> Term -> TCM ()
newIFSMeta 	  :: String -> Type -> [(Term, Type)] -> TCM Term
newValueMeta      :: RunMetaOccursCheck -> Type -> TCM Term
newNamedValueMeta :: RunMetaOccursCheck -> String -> Type -> TCM Term
