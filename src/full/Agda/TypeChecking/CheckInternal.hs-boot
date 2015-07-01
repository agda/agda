module Agda.TypeChecking.CheckInternal where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base (TCM)

checkType :: Type -> TCM ()
checkInternal :: Term -> Type -> TCM ()
infer :: Term -> TCM Type
