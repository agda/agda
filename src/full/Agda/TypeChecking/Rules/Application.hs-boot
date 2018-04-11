
module Agda.TypeChecking.Rules.Application where

import Agda.Syntax.Common (NamedArg)
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Except ( ExceptT )

checkArguments :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Type ->
                  ExceptT (Elims, [NamedArg A.Expr], Type) TCM (Elims, Type)

checkArguments' :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Type ->
                   (Elims-> Type -> TCM Term) -> TCM Term

checkArguments_ :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Telescope ->
                   TCM (Elims, Telescope)

checkApplication :: A.Expr -> A.Args -> A.Expr -> Type -> TCM Term

checkHeadApplication :: A.Expr -> Type -> A.Expr -> [NamedArg A.Expr] -> TCM Term

inferHead :: A.Expr -> TCM (Elims -> Term, Type)
