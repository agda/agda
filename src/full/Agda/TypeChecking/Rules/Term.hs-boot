
module Agda.TypeChecking.Rules.Term where

import Agda.Syntax.Common (WithHiding)
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal as I
import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Except ( ExceptT )

isType_ :: A.Expr -> TCM Type

checkExpr :: A.Expr -> Type -> TCM Term

checkArguments :: ExpandHidden -> ExpandInstances -> Range -> [NamedArg A.Expr] -> Type -> Type ->
                  ExceptT (Args, [NamedArg A.Expr], Type) TCM (Args, Type)

checkArguments' :: ExpandHidden -> ExpandInstances -> Range -> [NamedArg A.Expr] -> Type -> Type ->
                   (Args -> Type -> TCM Term) -> TCM Term

checkPostponedLambda :: I.Arg ([WithHiding Name], Maybe Type) -> A.Expr -> Type -> TCM Term
