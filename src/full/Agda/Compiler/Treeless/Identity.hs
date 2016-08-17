
module Agda.Compiler.Treeless.Identity where

import Agda.Syntax.Treeless
import Agda.TypeChecking.Substitute
import Agda.TypeChecking.Monad

detectIdentityFunctions :: TTerm -> TCM TTerm
detectIdentityFunctions t = return t
