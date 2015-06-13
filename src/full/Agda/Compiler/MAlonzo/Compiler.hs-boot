module Agda.Compiler.MAlonzo.Compiler where

import qualified Language.Haskell.Exts.Syntax as HS

import Agda.Syntax.Internal (Term)
import Agda.TypeChecking.Monad (TCM)

closedTerm :: Term -> TCM HS.Exp
