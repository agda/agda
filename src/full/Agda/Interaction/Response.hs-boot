module Agda.Interaction.Response where

import Data.Int (Int32)

import Agda.Syntax.Common   (InteractionId)
import Agda.Syntax.Concrete (Expr)

import {-# SOURCE #-} Agda.TypeChecking.Monad.Base
    (TCM, ModuleToSource, HighlightingMethod)

import Agda.Interaction.Highlighting.Precise
    (TokenBased, HighlightingInfo)

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
    | Resp_MakeCase InteractionId MakeCaseVariant [String]
    | Resp_SolveAll [(InteractionId, Expr)]
    | Resp_DisplayInfo DisplayInfo
    | Resp_RunningInfo Int String
    | Resp_ClearRunningInfo
    | Resp_ClearHighlighting TokenBased
    | Resp_DoneAborting

data MakeCaseVariant
data DisplayInfo
data RemoveTokenBasedHighlighting
data GiveResult
data Status

type InteractionOutputCallback = Response -> TCM ()
defaultInteractionOutputCallback :: InteractionOutputCallback
