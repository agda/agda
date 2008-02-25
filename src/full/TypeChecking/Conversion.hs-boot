
module TypeChecking.Conversion where

import Data.Generics
import Syntax.Internal
import TypeChecking.Monad

equalTerm :: MonadTCM tcm => Type -> Term -> Term -> tcm Constraints
equalArgs :: MonadTCM tcm => Type -> Args -> Args -> tcm Constraints
equalType :: MonadTCM tcm => Type -> Type -> tcm Constraints
equalSort :: MonadTCM tcm => Sort -> Sort -> tcm Constraints
leqSort   :: MonadTCM tcm => Sort -> Sort -> tcm Constraints


