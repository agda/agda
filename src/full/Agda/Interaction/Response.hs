------------------------------------------------------------------------
-- | Data type for all interactive responses
------------------------------------------------------------------------
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Agda.Interaction.Response
  ( Response (..)
  ) where

import Agda.Interaction.Highlighting.Precise
--import Agda.Interaction.MakeCase
import Agda.TypeChecking.Monad.Base
import Agda.Syntax.Concrete (Expr)
--import Agda.Utils.Pretty

import Data.Int


-- | Responses for any interactive interface
--
--   Note that the response is given in pieces and incrementally,
--   so the user can have timely response even during long computations.

data Response
    = Resp_HighlightingInfo HighlightingInfo
    | Resp_Status String
    | Resp_UpdateHighlighting FilePath
    | Resp_JumpToError FilePath Int32
    | Resp_InteractionPoints [InteractionId]
    | Resp_GiveAction InteractionId String
    | Resp_MakeCaseAction [String]
    | Resp_MakeCase String [String] -- CaseContext, [Doc]
    | Resp_SolveAll [(InteractionId, Expr)]
    | Resp_DisplayInfo String String
    | Resp_RunningInfo String
    | Resp_ClearRunningInfo

