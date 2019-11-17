module Agda.TypeChecking.MetaVars where

import Agda.Syntax.Common           ( Arg )
import Agda.Syntax.Internal         ( MetaId, Term, Type, Args, Dom, Abs, Telescope, Sort )
import Agda.TypeChecking.Monad.Base ( TCM, RunMetaOccursCheck, Comparison, CompareAs, CompareDirection )
import Agda.TypeChecking.Monad.MetaVars   ( MonadMetaSolver )

-- Imports for expandProjectedVars:
-- import Agda.Syntax.Internal.Generic       ( TermLike )
import Agda.TypeChecking.Pretty           ( PrettyTCM )
-- import Agda.TypeChecking.Reduce           ( Reduce )
import Agda.TypeChecking.Substitute.Class ( Subst )

instance MonadMetaSolver TCM

type Condition = Dom Type -> Abs Type -> Bool
newArgsMeta'      :: MonadMetaSolver m => Condition -> Type -> m Args
newArgsMeta       :: MonadMetaSolver m => Type -> m Args
assignTerm        :: MonadMetaSolver m => MetaId -> [Arg String] -> Term -> m ()
etaExpandMetaSafe :: MonadMetaSolver m => MetaId -> m ()
assign            :: CompareDirection -> MetaId -> Args -> Term -> CompareAs -> TCM ()
newInstanceMeta   :: MonadMetaSolver m => String -> Type -> m (MetaId, Term)
newValueMeta      :: MonadMetaSolver m => RunMetaOccursCheck -> Comparison -> Type -> m (MetaId, Term)
newNamedValueMeta :: MonadMetaSolver m => RunMetaOccursCheck -> String -> Comparison -> Type -> m (MetaId, Term)
newNamedValueMeta':: MonadMetaSolver m => RunMetaOccursCheck -> String -> Comparison -> Type -> m (MetaId, Term)
newTelMeta        :: MonadMetaSolver m => Telescope -> m Args
newSortMeta       :: TCM Sort
checkMetaInst     :: MetaId -> TCM ()

-- Definitions for expandProjectedVars:

class    NoProjectedVar a
instance NoProjectedVar Term
instance NoProjectedVar a => NoProjectedVar (Arg a)
instance NoProjectedVar a => NoProjectedVar [a]

class    ReduceAndEtaContract a
instance ReduceAndEtaContract Term
instance ReduceAndEtaContract a => ReduceAndEtaContract (Arg a)
instance ReduceAndEtaContract a => ReduceAndEtaContract [a]

expandProjectedVars :: ( Show a, PrettyTCM a, NoProjectedVar a, ReduceAndEtaContract a
                       , PrettyTCM b, Subst Term b
                       ) => a -> b -> (Bool -> a -> b -> TCM c) -> TCM c
