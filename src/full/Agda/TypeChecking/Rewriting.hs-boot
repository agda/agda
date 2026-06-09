{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Rewriting where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.Utils.CallStack (HasCallStack)

verifyBuiltinRewrite :: Term -> Type -> TCM ()
rewrite :: HasCallStack => Blocked_ -> (Elims -> Term) -> RewriteRules -> Elims -> ReduceM (Reduced (Blocked Term) Term)
checkRewConstraint :: LocalEquation -> TCM ()
