
module TypeChecking.Conversion where

import Data.Generics
import Syntax.Internal
import TypeChecking.Monad

equalVal  :: Type -> Term -> Term -> TCM ()
equalTyp  :: Type -> Type -> TCM ()
equalSort :: Sort -> Sort -> TCM ()
leqSort   :: Sort -> Sort -> TCM ()


