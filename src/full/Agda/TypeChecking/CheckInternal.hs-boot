module Agda.TypeChecking.CheckInternal where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base (TCM)

data Action

defaultAction :: Action
eraseUnusedAction :: Action

checkType :: Type -> TCM ()
checkType' :: Type -> TCM Sort
checkSort :: Action -> Sort -> TCM Sort
checkInternal :: Term -> Type -> TCM ()
checkInternal' :: Action -> Term -> Type -> TCM Term
infer :: Term -> TCM Type
shouldBeSort :: Type -> TCM Sort
