module Agda.TypeChecking.Monad.Options where


import Agda.Interaction.Library
import Agda.TypeChecking.Monad.Base
import Agda.Utils.FileName

getIncludeDirs :: HasOptions m => m LibAbsolutePaths

enableCaching :: HasOptions m => m Bool
