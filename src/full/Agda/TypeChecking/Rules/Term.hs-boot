
module Agda.TypeChecking.Rules.Term where

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base

checkExpr :: A.Expr -> Type -> TCM Term

