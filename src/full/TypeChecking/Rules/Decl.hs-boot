
module TypeChecking.Rules.Decl where

import Syntax.Abstract (Declaration)
import TypeChecking.Monad (TCM)

checkDecls :: [Declaration] -> TCM ()

