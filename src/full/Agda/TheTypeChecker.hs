{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TheTypeChecker
  ( checkDecls, checkDecl, checkDeclCached
  , inferExpr, checkExpr
  ) where

import Agda.TypeChecking.Rules.Decl
import Agda.TypeChecking.Rules.Term
