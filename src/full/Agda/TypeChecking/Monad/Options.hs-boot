module Agda.TypeChecking.Monad.Options where

import Agda.TypeChecking.Monad.Base
import Agda.Utils.FileName
import Agda.Utils.Pretty

getIncludeDirs :: TCM [AbsolutePath]

type VerboseKey = String

verboseS :: MonadTCM tcm => VerboseKey -> Int -> tcm () -> tcm ()
reportSLn :: MonadTCM tcm => VerboseKey -> Int -> String -> tcm ()
reportSDoc :: MonadTCM tcm => VerboseKey -> Int -> TCM Doc -> tcm ()
