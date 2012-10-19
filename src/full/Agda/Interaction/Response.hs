------------------------------------------------------------------------
-- | Data type for all interactive responses
------------------------------------------------------------------------
{-# LANGUAGE CPP, TypeSynonymInstances, FlexibleInstances #-}

module Agda.Interaction.Response
  ( Response (..)
  , DisplayInfo (..)
  , Status (..)
  , GiveResult (..)
  , InteractionOutputCallback
  , defaultInteractionOutputCallback
  ) where

import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.FindFile (ModuleToSource)
--import Agda.Interaction.MakeCase
import Agda.TypeChecking.Monad.Base
import Agda.Syntax.Concrete (Expr)
import Agda.Utils.Pretty

import Data.Int

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Responses for any interactive interface
--
--   Note that the response is given in pieces and incrementally,
--   so the user can have timely response even during long computations.

data Response
    = Resp_HighlightingInfo HighlightingInfo ModuleToSource
    | Resp_Status Status
    | Resp_JumpToError FilePath Int32
    | Resp_InteractionPoints [InteractionId]
    | Resp_GiveAction InteractionId GiveResult
    | Resp_MakeCaseAction [String]
    | Resp_MakeCase String [String]
    | Resp_SolveAll [(InteractionId, Expr)]
    | Resp_DisplayInfo DisplayInfo
    | Resp_RunningInfo String
    | Resp_ClearRunningInfo
    | Resp_ClearHighlighting

-- | Info to display at the end of an interactive command

data DisplayInfo
    = Info_CompilationOk
    | Info_Constraints String
    | Info_AllGoals String
    | Info_Error String
        -- ^ When an error message is displayed this constructor should be
        -- used, if appropriate.
    | Info_Intro Doc
        -- ^ 'Info_Intro' denotes two different types of errors
        --   TODO: split these into separate constructors
    | Info_Auto String
        -- ^ 'Info_Auto' denotes either an error or a success (when 'Resp_GiveAction' is present)
        --   TODO: split these into separate constructors
    | Info_ModuleContents Doc
    | Info_NormalForm Doc
    | Info_GoalType Doc
    | Info_CurrentGoal Doc
    | Info_InferredType Doc
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

-- | Callback fuction to call when there is a response
--   to give to the interactive frontend.
--
--   Note that the response is given in pieces and incrementally,
--   so the user can have timely response even during long computations.
--
--   Typical 'InteractionOutputCallback' functions:
--
--    * Convert the response into a 'String' representation and
--      print it on standard output
--      (suitable for inter-process communication).
--
--    * Put the response into a mutable variable stored in the
--      closure of the 'InteractionOutputCallback' function.
--      (suitable for intra-process communication).

type InteractionOutputCallback = Response -> TCM ()

-- | The default 'InteractionOutputCallback' function
--   is set to @__@@IMPOSSIBLE__@ because in this way it is easier to
--   recognize that some response is lost due to an uninitialized
--   'InteractionOutputCallback' function.

defaultInteractionOutputCallback :: InteractionOutputCallback
defaultInteractionOutputCallback = __IMPOSSIBLE__
