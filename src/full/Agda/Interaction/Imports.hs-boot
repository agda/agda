
module Agda.Interaction.Imports where

import Agda.Syntax.Abstract.Name    ( ModuleName )
import Agda.Syntax.Scope.Base       ( Scope )
import Agda.TypeChecking.Monad.Base ( TCM, TCWarning )
import Agda.TypeChecking.Warnings   ( WhichWarnings )
import Data.Map                     ( Map )

data MaybeWarnings' a = NoWarnings | SomeWarnings a
type MaybeWarnings = MaybeWarnings' [TCWarning]
instance Functor MaybeWarnings'

data Mode
data MainInterface = MainInterface Mode | NotMainInterface

instance Eq MainInterface

scopeCheckImport :: ModuleName -> TCM (ModuleName, Map ModuleName Scope)
getMaybeWarnings :: WhichWarnings -> TCM MaybeWarnings
