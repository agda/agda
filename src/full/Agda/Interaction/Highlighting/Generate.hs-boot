{-# OPTIONS_GHC -Wunused-imports #-}

module Agda.Interaction.Highlighting.Generate where

import Agda.TypeChecking.Monad.Base (TCM, TCWarning)

highlightWarning :: TCWarning -> TCM ()
