
module Agda.Interaction.Output where

import Agda.Interaction.Base

import Agda.TypeChecking.Monad.Base (TCErr)

--------------------------
-- * TCM-aware aliases
--------------------------

type OutputForm a b = OutputForm_boot TCErr a b

type OutputConstraint a b = OutputConstraint_boot TCErr a b
