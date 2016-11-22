module Agda.Compiler.MAlonzo.Compiler where

import qualified Agda.Utils.Haskell.Syntax as HS

import Agda.Syntax.Treeless (TTerm)
import Agda.TypeChecking.Monad (TCM)

closedTerm :: TTerm -> TCM HS.Exp
