module Agda.TypeChecking.Monad.Options where



import Agda.TypeChecking.Monad.Base
import Agda.Utils.FileName

getIncludeDirs :: HasOptions m => m [AbsolutePath]

enableCaching :: HasOptions m => m Bool
