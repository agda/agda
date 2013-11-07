
module Agda.TypeChecker
  ( checkDecls, checkDecl
  , inferExpr, checkExpr
  ) where

import Agda.TypeChecking.Rules.Decl    as Rules
import Agda.TypeChecking.Rules.Term    as Rules
