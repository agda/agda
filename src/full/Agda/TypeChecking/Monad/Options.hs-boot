module Agda.TypeChecking.Monad.Options where

import Control.Applicative
import Control.Monad.Trans

import Agda.Interaction.Options
import Agda.TypeChecking.Monad.Base
import Agda.Utils.FileName
import Agda.Utils.Pretty

getIncludeDirs :: TCM [AbsolutePath]

type VerboseKey = String

hasVerbosity :: HasOptions m => VerboseKey -> Int -> m Bool
verboseS :: HasOptions m => VerboseKey -> Int -> m () -> m ()
reportSLn :: (HasOptions m, MonadDebug m)
          => VerboseKey -> Int -> String -> m ()
reportSDoc :: MonadTCM tcm => VerboseKey -> Int -> TCM Doc -> tcm ()
