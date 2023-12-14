
module Agda.Interaction.Response
    ( module Agda.Interaction.Response
    , module Agda.Interaction.Response.Base
    , WarningsAndNonFatalErrors
    , InteractionOutputCallback
    , defaultInteractionOutputCallback
    )
    where

import Agda.Interaction.Response.Base

import Agda.TypeChecking.Monad.Base
  (TCM, TCErr, TCWarning, InteractionOutputCallback, defaultInteractionOutputCallback)
import Agda.TypeChecking.Warnings (WarningsAndNonFatalErrors)

--------------------------
-- * TCM-aware aliases
--------------------------

type Response        = Response_boot        TCErr TCWarning WarningsAndNonFatalErrors
type DisplayInfo     = DisplayInfo_boot     TCErr TCWarning WarningsAndNonFatalErrors
type Info_Error      = Info_Error_boot      TCErr TCWarning
type GoalDisplayInfo = GoalDisplayInfo_boot TCErr
type Goals           = Goals_boot           TCErr
