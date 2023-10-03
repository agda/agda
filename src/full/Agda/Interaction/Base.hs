
module Agda.Interaction.Base
    ( module Agda.Interaction.Base
    , module Agda.Interaction.Base.Types
    ) where

import Agda.Interaction.Base.Types

import Agda.TypeChecking.Monad.Base (TCM, TCErr)

import Control.Monad.State

--------------------------
-- * TCM-aware aliases
--------------------------

type OutputForm a b = OutputForm_boot TCErr a b

type OutputConstraint a b = OutputConstraint_boot TCErr a b

-- | Monad for computing answers to interactive commands.
--
--   'CommandM' is 'TCM' extended with state 'CommandState'.

type CommandM = StateT CommandState TCM
