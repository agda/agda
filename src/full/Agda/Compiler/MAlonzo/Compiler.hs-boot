module Agda.Compiler.MAlonzo.Compiler where

import Control.Monad.Reader (ReaderT)
import Language.Haskell.Syntax (HsExp)

import Agda.Syntax.Common (Nat)
import Agda.Syntax.Internal (Term)
import Agda.TypeChecking.Monad (TCM)

term :: Term -> ReaderT Nat TCM HsExp
