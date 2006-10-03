
module TypeChecker where

import Syntax.Abstract.Name    ( ModuleName )
import Syntax.ScopeInfo	       ( ModuleScope )
import TypeChecking.Monad.Base ( TCM )

scopeCheckImport :: ModuleName -> TCM ModuleScope

