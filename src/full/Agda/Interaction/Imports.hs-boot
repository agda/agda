
module Agda.Interaction.Imports where

import Data.Map                     ( Map )

import Agda.Syntax.Abstract.Name    ( ModuleName )
import Agda.Syntax.Scope.Base       ( Scope )
import Agda.TypeChecking.Monad.Base ( TCM )

scopeCheckImport :: ModuleName -> TCM (ModuleName, Map ModuleName Scope)
