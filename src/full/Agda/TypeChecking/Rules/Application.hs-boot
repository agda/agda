
module Agda.TypeChecking.Rules.Application where

import Agda.Syntax.Common (NamedArg)
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base

checkArguments :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Type ->
                  (Elims -> Type -> CheckedTarget -> TCM Term) -> TCM Term

checkArguments_ :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Telescope ->
                   TCM (Elims, Telescope)

checkApplication :: A.Expr -> A.Args -> A.Expr -> Type -> TCM Term

inferApplication :: ExpandHidden -> A.Expr -> A.Args -> A.Expr -> TCM (Term, Type)
