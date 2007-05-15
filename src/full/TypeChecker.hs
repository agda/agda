
module TypeChecker
  ( checkDecls, checkDecl
  , inferExpr, checkExpr
  ) where

import TypeChecking.Rules.Builtin as Rules
import TypeChecking.Rules.Data	  as Rules
import TypeChecking.Rules.Decl	  as Rules
import TypeChecking.Rules.Def	  as Rules
import TypeChecking.Rules.LHS	  as Rules
import TypeChecking.Rules.Pattern as Rules
import TypeChecking.Rules.Record  as Rules
import TypeChecking.Rules.Term	  as Rules

