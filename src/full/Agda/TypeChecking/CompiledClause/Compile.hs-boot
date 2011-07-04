module Agda.TypeChecking.CompiledClause.Compile where

import Agda.Syntax.Internal
import Agda.TypeChecking.CompiledClause
import Agda.TypeChecking.Monad.Base

compileClauses ::
  MonadTCM tcm => Bool -> [Clause] -> tcm CompiledClauses
