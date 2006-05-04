
module TypeChecking.Conversion where

import Data.Generics
import Syntax.Internal
import TypeChecking.Monad

equalVal :: Data a => a -> Type -> Term -> Term -> TCM ()
equalTyp :: Data a => a -> Type -> Type -> TCM ()

