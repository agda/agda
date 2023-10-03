
module Agda.Interaction.Response
    (   module Agda.Interaction.Response
    ,   module Agda.Interaction.Response.Boot
    ,   WarningsAndNonFatalErrors
    ,   InteractionOutputCallback
    ,   defaultInteractionOutputCallback
    )
    where

import Agda.Interaction.Response.Boot

import Agda.TypeChecking.Monad.Base (TCM, TCErr, TCWarning)
import Agda.TypeChecking.Warnings (WarningsAndNonFatalErrors)

import Agda.TypeChecking.Monad.Base  (InteractionOutputCallback, defaultInteractionOutputCallback)

--------------------------
-- * TCM-aware aliases
--------------------------

type Response = Response_boot TCErr TCWarning WarningsAndNonFatalErrors

type DisplayInfo = DisplayInfo_boot TCErr TCWarning WarningsAndNonFatalErrors

type Info_Error = Info_Error_boot TCErr TCWarning

type GoalDisplayInfo = GoalDisplayInfo_boot TCWarning

type Goals = Goals_boot TCErr
