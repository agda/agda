module Agda.TypeChecking.Rewriting where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

verifyBuiltinRewrite :: Term -> Type -> TCM ()
rewrite :: Blocked_ -> Term -> RewriteRules -> Elims -> ReduceM (Reduced (Blocked Term) Term)
