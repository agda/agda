
module Agda.TypeChecking.Rules.Term where

import Agda.Syntax.Common (WithHiding, Arg)
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.Utils.List1 (List1)

isType_ :: A.Expr -> TCM Type

checkExpr :: A.Expr -> Type -> TCM Term
checkExpr' :: Comparison -> A.Expr -> Type -> TCM Term
inferExpr :: A.Expr -> TCM (Term, Type)

doQuoteTerm :: Comparison -> Term -> Type -> TCM Term
unquoteTactic :: Term -> Term -> Type -> TCM ()
