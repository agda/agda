
module Agda.TypeChecking.Rules.Term where

import Agda.Syntax.Common (WithHiding, NamedArg, Arg)
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Except ( ExceptT )

isType_ :: A.Expr -> TCM Type

checkExpr :: A.Expr -> Type -> TCM Term
inferExpr :: A.Expr -> TCM (Term, Type)

checkArguments :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Type ->
                  ExceptT (Args, [NamedArg A.Expr], Type) TCM (Args, Type)

checkArguments' :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Type ->
                   (Args -> Type -> TCM Term) -> TCM Term

checkPostponedLambda :: Arg ([WithHiding Name], Maybe Type) -> A.Expr -> Type -> TCM Term

unquoteTactic :: Term -> Term -> Type -> TCM Term -> TCM Term
