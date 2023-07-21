{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.CompiledClause.Compile where

import Agda.Syntax.Internal
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Coverage.SplitTree
import Agda.TypeChecking.Monad.Base

compileClauses :: Maybe (QName, Type) -> [Clause] -> TCM (Maybe SplitTree, Bool, CompiledClauses)
