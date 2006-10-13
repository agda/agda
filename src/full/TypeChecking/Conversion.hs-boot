
module TypeChecking.Conversion where

import Data.Generics
import Syntax.Internal
import TypeChecking.Monad

equalVal  :: Type -> Term -> Term -> TCM Constraints
equalTyp  :: Type -> Type -> TCM Constraints
equalSort :: Sort -> Sort -> TCM Constraints
leqSort   :: Sort -> Sort -> TCM Constraints


