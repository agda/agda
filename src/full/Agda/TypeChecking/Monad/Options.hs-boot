module Agda.TypeChecking.Monad.Options where

import Control.Applicative
import Control.Monad.Trans

import Agda.Interaction.Options
import Agda.TypeChecking.Monad.Base
import Agda.Utils.FileName
import Agda.Utils.Pretty

getIncludeDirs :: TCM [AbsolutePath]

type VerboseKey = String

class (Functor m, Applicative m, Monad m) => HasOptions m where
  -- | Returns the pragma options which are currently in effect.
  pragmaOptions      :: m PragmaOptions
  -- | Returns the command line options which are currently in effect.
  commandLineOptions :: m CommandLineOptions

instance MonadIO m => HasOptions (TCMT m)

hasVerbosity :: HasOptions m => VerboseKey -> Int -> m Bool
verboseS :: MonadTCM tcm => VerboseKey -> Int -> tcm () -> tcm ()
reportSLn :: MonadTCM tcm => VerboseKey -> Int -> String -> tcm ()
reportSDoc :: MonadTCM tcm => VerboseKey -> Int -> TCM Doc -> tcm ()
