module Agda.TypeChecking.CompiledClause.Compile where

import Agda.Syntax.Internal
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad.Base

compileClauses :: Bool -> [Clause] -> TCM CompiledClauses
