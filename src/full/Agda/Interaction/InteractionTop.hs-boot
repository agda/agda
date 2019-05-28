module Agda.Interaction.InteractionTop where

import Agda.TypeChecking.Monad.Base (TCM)
import Agda.Interaction.BasicOps (Goals)

showGoals :: Goals -> TCM String
