
module Agda.TypeChecking.CompiledClause.Match where

import Agda.Syntax.Common
import Agda.Syntax.Internal
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.CompiledClause

matchCompiled :: CompiledClauses -> MaybeReducedArgs -> TCM (Reduced (Blocked Args) Term)
