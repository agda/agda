module Agda.TypeChecking.MetaVars where

import Agda.Syntax.Common           ( Arg, Dom )
import Agda.Syntax.Internal         ( MetaId, Term, Type, Args, Abs, Telescope, Sort )
import Agda.TypeChecking.Monad.Base ( TCM, RunMetaOccursCheck, CompareDirection )
import Agda.TypeChecking.Monad.MetaVars (MonadMetaSolver)

instance MonadMetaSolver TCM

type Condition = Dom Type -> Abs Type -> Bool
newArgsMeta'      :: Condition -> Type -> TCM Args
newArgsMeta       :: Type -> TCM Args
assignTerm        :: MonadMetaSolver m => MetaId -> [Arg String] -> Term -> m ()
etaExpandMetaSafe :: MonadMetaSolver m => MetaId -> m ()
assign            :: CompareDirection -> MetaId -> Args -> Term -> TCM ()
newInstanceMeta   :: String -> Type -> TCM (MetaId, Term)
newValueMeta      :: RunMetaOccursCheck -> Type -> TCM (MetaId, Term)
newNamedValueMeta :: RunMetaOccursCheck -> String -> Type -> TCM (MetaId, Term)
newNamedValueMeta':: RunMetaOccursCheck -> String -> Type -> TCM (MetaId, Term)
newTelMeta        :: Telescope -> TCM Args
newSortMeta       :: TCM Sort
