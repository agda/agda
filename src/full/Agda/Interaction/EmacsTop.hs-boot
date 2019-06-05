module Agda.Interaction.EmacsTop where

import Agda.TypeChecking.Monad.Base (TCM)
import Agda.Interaction.Response (Goals)

showGoals :: Goals -> TCM String
