
module Agda.TypeChecker
  ( checkDecls, checkDecl
  , inferExpr, checkExpr
  ) where

import Agda.TypeChecking.Rules.Decl
import Agda.TypeChecking.Rules.Term
