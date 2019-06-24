module Agda.Interaction.Response where

import Agda.Interaction.Highlighting.Precise
    (TokenBased, HighlightingInfo)
import Agda.Syntax.Common   (InteractionId)
import Agda.Syntax.Concrete (Expr, Name)
import {-# SOURCE #-} Agda.TypeChecking.Monad.Base
    (TCM, ModuleToSource, HighlightingMethod)
import Data.Int (Int32)

data Response
    = Resp_HighlightingInfo
        HighlightingInfo
        RemoveTokenBasedHighlighting
        HighlightingMethod
        ModuleToSource
    | Resp_Status Status
    | Resp_JumpToError FilePath Int32
    | Resp_InteractionPoints [InteractionId]
    | Resp_GiveAction InteractionId GiveResult
    | Resp_MakeCase MakeCaseVariant [String]
    | Resp_SolveAll [(InteractionId, Expr)]
      -- ^ Solution for one or more meta-variables.
    | Resp_DisplayInfo DisplayInfo
    | Resp_RunningInfo Int String
      -- ^ The integer is the message's debug level.
    | Resp_ClearRunningInfo
    | Resp_ClearHighlighting TokenBased
      -- ^ Clear highlighting of the given kind.
    | Resp_DoneAborting

data MakeCaseVariant
data DisplayInfo
data RemoveTokenBasedHighlighting
data GiveResult
data Status

type InteractionOutputCallback = Response -> TCM ()
defaultInteractionOutputCallback :: InteractionOutputCallback
