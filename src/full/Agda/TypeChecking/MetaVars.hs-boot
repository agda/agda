module Agda.TypeChecking.MetaVars where

import Agda.Syntax.Common           ( Arg )
import Agda.Syntax.Internal         ( MetaId, Term, Type, Args, Dom, Abs, Telescope, Sort )
import Agda.TypeChecking.Monad.Base ( TCM, RunMetaOccursCheck, Comparison, CompareAs, CompareDirection )
import Agda.TypeChecking.Monad.MetaVars (MonadMetaSolver)

instance MonadMetaSolver TCM

type Condition = Dom Type -> Abs Type -> Bool
newArgsMeta'      :: MonadMetaSolver m => Condition -> Type -> m Args
newArgsMeta       :: MonadMetaSolver m => Type -> m Args
assignTerm        :: MonadMetaSolver m => MetaId -> [Arg String] -> Term -> m ()
assign            :: CompareDirection -> MetaId -> Args -> Term -> CompareAs -> TCM ()
newInstanceMeta   :: MonadMetaSolver m => String -> Type -> m (MetaId, Term)
newValueMeta      :: MonadMetaSolver m => RunMetaOccursCheck -> Comparison -> Type -> m (MetaId, Term)
newNamedValueMeta :: MonadMetaSolver m => RunMetaOccursCheck -> String -> Comparison -> Type -> m (MetaId, Term)
newNamedValueMeta':: MonadMetaSolver m => RunMetaOccursCheck -> String -> Comparison -> Type -> m (MetaId, Term)
newTelMeta        :: MonadMetaSolver m => Telescope -> m Args
newSortMeta       :: MonadMetaSolver m => m Sort
checkMetaInst     :: MetaId -> TCM ()
