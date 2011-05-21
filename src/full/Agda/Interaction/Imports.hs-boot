
module Agda.Interaction.Imports where

import Agda.Syntax.Abstract.Name    ( ModuleName )
import Agda.Syntax.Scope.Base       ( Scope )
import Agda.TypeChecking.Monad.Base ( TCM )
import Data.Map                     ( Map )

scopeCheckImport :: ModuleName -> TCM (ModuleName, Map ModuleName Scope)
