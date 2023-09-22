{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Monad.Options where

import Agda.Interaction.Library.Base
import Agda.Interaction.Options.HasOptions
import Agda.TypeChecking.Monad.Base
import Agda.Utils.FileName

libToTCM       :: LibM a -> TCM a
getIncludeDirs :: HasOptions m => m [AbsolutePath]
