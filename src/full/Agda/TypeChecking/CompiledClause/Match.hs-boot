
module Agda.TypeChecking.CompiledClause.Match where

import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.CompiledClause

matchCompiled :: CompiledClauses -> Args -> TCM (Reduced (Blocked Args) Term)

