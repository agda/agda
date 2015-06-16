module Agda.TypeChecking.Rewriting where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

verifyBuiltinRewrite :: Term -> Type -> TCM ()
rewrite :: Blocked Term -> ReduceM (Either (Blocked Term) Term)
