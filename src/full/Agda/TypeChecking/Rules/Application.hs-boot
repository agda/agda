
module Agda.TypeChecking.Rules.Application where

import Agda.Syntax.Common (NamedArg)
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import Agda.Utils.Except ( ExceptT )

checkArguments :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Type ->
                  ExceptT (Args, [NamedArg A.Expr], Type) TCM (Args, Type)

checkArguments' :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Type -> Type ->
                   (Args -> Type -> TCM Term) -> TCM Term

checkArguments_ :: ExpandHidden -> Range -> [NamedArg A.Expr] -> Telescope ->
                   TCM (Args, Telescope)

checkApplication :: A.Expr -> A.Args -> A.Expr -> Type -> TCM Term

checkHeadApplication :: A.Expr -> Type -> A.Expr -> [NamedArg A.Expr] -> TCM Term

inferHead :: A.Expr -> TCM (Args -> Term, Type)
