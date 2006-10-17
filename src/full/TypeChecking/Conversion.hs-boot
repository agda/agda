
module TypeChecking.Conversion where

import Data.Generics
import Syntax.Internal
import TypeChecking.Monad

equalTerm :: Type -> Term -> Term -> TCM Constraints
equalType :: Type -> Type -> TCM Constraints
equalSort :: Sort -> Sort -> TCM Constraints
leqSort   :: Sort -> Sort -> TCM Constraints


