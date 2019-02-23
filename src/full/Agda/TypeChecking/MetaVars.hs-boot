module Agda.TypeChecking.MetaVars where

import Agda.Syntax.Common           ( Arg, Dom )
import Agda.Syntax.Internal         ( MetaId, Term, Type, Args, Abs, Telescope, Sort )
import Agda.TypeChecking.Monad.Base ( TCM, RunMetaOccursCheck, CompareDirection )
import Agda.TypeChecking.Monad.MetaVars (MonadMetaSolver)

instance MonadMetaSolver TCM

type Condition = Dom Type -> Abs Type -> Bool
newArgsMeta'      :: MonadMetaSolver m => Condition -> Type -> m Args
newArgsMeta       :: MonadMetaSolver m => Type -> m Args
assignTerm        :: MonadMetaSolver m => MetaId -> [Arg String] -> Term -> m ()
etaExpandMetaSafe :: MonadMetaSolver m => MetaId -> m ()
assign            :: CompareDirection -> MetaId -> Args -> Term -> TCM ()
newInstanceMeta   :: String -> Type -> TCM (MetaId, Term)
newValueMeta      :: MonadMetaSolver m => RunMetaOccursCheck -> Type -> m (MetaId, Term)
newNamedValueMeta :: RunMetaOccursCheck -> String -> Type -> TCM (MetaId, Term)
newNamedValueMeta':: RunMetaOccursCheck -> String -> Type -> TCM (MetaId, Term)
newTelMeta        :: MonadMetaSolver m => Telescope -> m Args
newSortMeta       :: TCM Sort
