
module TypeChecking.Rules.Term where

import qualified Syntax.Abstract as A
import Syntax.Internal
import TypeChecking.Monad.Base

checkExpr :: A.Expr -> Type -> TCM Term

