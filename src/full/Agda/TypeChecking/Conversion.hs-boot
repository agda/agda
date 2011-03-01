
module Agda.TypeChecking.Conversion where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad

compareTerm :: MonadTCM tcm => Comparison -> Type -> Term -> Term -> tcm Constraints
compareAtom :: MonadTCM tcm => Comparison -> Type -> Term -> Term -> tcm Constraints
compareArgs :: MonadTCM tcm => [Polarity] -> Type -> Args -> Args -> tcm Constraints
compareType :: MonadTCM tcm => Comparison -> Type -> Type -> tcm Constraints
compareTel  :: MonadTCM tcm => Comparison -> Telescope -> Telescope -> tcm Constraints
compareSort :: MonadTCM tcm => Comparison -> Sort -> Sort -> tcm Constraints
equalTerm :: MonadTCM tcm => Type -> Term -> Term -> tcm Constraints
equalArgs :: MonadTCM tcm => Type -> Args -> Args -> tcm Constraints
equalType :: MonadTCM tcm => Type -> Type -> tcm Constraints
equalSort :: MonadTCM tcm => Sort -> Sort -> tcm Constraints
leqType :: MonadTCM tcm => Type -> Type -> tcm Constraints
