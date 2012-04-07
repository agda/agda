------------------------------------------------------------------------
-- | Data type for all interactive responses
------------------------------------------------------------------------
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Agda.Interaction.Response
  ( Response (..)
  , DisplayInfo (..)
  , Status (..)
  , GiveResult (..)
  ) where

import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.FindFile (ModuleToSource)
--import Agda.Interaction.MakeCase
import Agda.TypeChecking.Monad.Base
import Agda.Syntax.Concrete (Expr)
import Agda.Utils.Pretty

import Data.Int


-- | Responses for any interactive interface
--
--   Note that the response is given in pieces and incrementally,
--   so the user can have timely response even during long computations.

data Response
    = Resp_HighlightingInfo HighlightingInfo
    | Resp_UpdateHighlighting (HighlightingInfo, ModuleToSource)
    | Resp_Status Status
    | Resp_JumpToError FilePath Int32
    | Resp_InteractionPoints [InteractionId]
    | Resp_GiveAction InteractionId GiveResult
    | Resp_MakeCaseAction [String]
    | Resp_MakeCase String [String] -- CaseContext, [Doc]
    | Resp_SolveAll [(InteractionId, Expr)]
    | Resp_DisplayInfo DisplayInfo
    | Resp_RunningInfo String
    | Resp_ClearRunningInfo

-- | Info to display at the end of an interactive command

data DisplayInfo
    = Info_CompilationOk

    | Info_Constraints String -- [B.OutputForm SC.Expr SC.Expr] -- unlines . map show
    | Info_AllGoals String -- (InteractionId, String, Maybe Range)

    | Info_Error String
        -- ^ When an error message is displayed this constructor should be
        -- used, if appropriate.
    | Info_Intro Doc  -- 2 different errors
    | Info_Auto String  -- 1 error, 1 ok (Resp_GiveAction)

    | Info_ModuleContents Doc
    | Info_NormalForm Doc -- show?   --  SA.Expr -- showA
    | Info_GoalType Doc
    | Info_CurrentGoal Doc
    | Info_InferredType Doc -- SA.Expr -- showA
    | Info_Context Doc
        deriving Show

-- | Status information.

data Status = Status
  { sShowImplicitArguments :: Bool
    -- ^ Are implicit arguments displayed?
  , sChecked               :: Bool
    -- ^ Has the module been successfully type checked?
  }

-- | Give action result
--
--   Comment derived from agda2-mode.el
--
--   If 'GiveResult' is 'Give_String s', then the goal is replaced by 's',
--   and otherwise the text inside the goal is retained (parenthesised
--   if 'GiveResult' is 'Give_Paren').

data GiveResult
    = Give_String String
    | Give_Paren
    | Give_NoParen

