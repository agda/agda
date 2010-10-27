
module Agda.TypeChecker
  ( checkDecls, checkDecl
  , inferExpr, checkExpr
  ) where

import Agda.TypeChecking.Rules.Builtin as Rules
import Agda.TypeChecking.Rules.Data    as Rules
import Agda.TypeChecking.Rules.Decl    as Rules
import Agda.TypeChecking.Rules.Def     as Rules
import Agda.TypeChecking.Rules.LHS     as Rules
import Agda.TypeChecking.Rules.Record  as Rules
import Agda.TypeChecking.Rules.Term    as Rules
