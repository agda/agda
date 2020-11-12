
module Agda.Interaction.Imports where

-- Control.Monad.Fail import is redundant since GHC 8.8.1
import Control.Monad.Fail (MonadFail)

import Data.Map                     ( Map )

import Agda.Syntax.Abstract.Name    ( ModuleName )
import Agda.Syntax.Scope.Base       ( Scope )
import Agda.TypeChecking.Monad.Base ( TCM, TCWarning, ReadTCState )
import Agda.TypeChecking.Warnings   ( WhichWarnings, MonadWarning )

data MaybeWarnings' a = NoWarnings | SomeWarnings a
type MaybeWarnings = MaybeWarnings' [TCWarning]
instance Functor MaybeWarnings'

scopeCheckImport :: ModuleName -> TCM (ModuleName, Map ModuleName Scope)
getAllWarnings :: (MonadFail m, ReadTCState m, MonadWarning m) => WhichWarnings -> m [TCWarning]
