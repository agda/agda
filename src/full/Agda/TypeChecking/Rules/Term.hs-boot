
module Agda.TypeChecking.Rules.Term where

import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Internal
import Agda.Syntax.Common hiding (Arg, Dom, NamedArg)
import Agda.Syntax.Position
import Agda.TypeChecking.Monad.Base
import Control.Monad.Error (ErrorT)

isType_ :: A.Expr -> TCM Type

checkExpr :: A.Expr -> Type -> TCM Term

checkArguments :: ExpandHidden -> ExpandInstances -> Range -> [NamedArg A.Expr] -> Type -> Type ->
                  ErrorT Type TCM (Args, Type)

