{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.TypeChecking.Monad.Options where

import Agda.Interaction.Library.Base
import Agda.TypeChecking.Monad.Base
import Agda.Utils.List1 (List1)

libToTCM       :: LibM a -> TCM a
getIncludeDirs :: TCM (List1 AbsolutePath)
