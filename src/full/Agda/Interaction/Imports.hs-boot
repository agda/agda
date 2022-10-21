
module Agda.Interaction.Imports where

import Data.Map                     ( Map )

import Agda.Syntax.Abstract.Name    ( ModuleName )
import Agda.Syntax.Scope.Base       ( Scope )
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)
import Agda.TypeChecking.Monad.Base ( TCM )

scopeCheckImport ::
  TopLevelModuleName -> ModuleName ->
  TCM (ModuleName, Map ModuleName Scope)
