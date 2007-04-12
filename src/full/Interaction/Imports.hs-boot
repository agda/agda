
module Interaction.Imports where

import Syntax.Abstract.Name    ( ModuleName )
import Syntax.Scope.Base       ( Scope )
import TypeChecking.Monad.Base ( TCM )

scopeCheckImport :: ModuleName -> TCM Scope

