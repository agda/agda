{-# LANGUAGE CPP #-}

------------------------------------------------------------------------
-- | Data type for all interactive responses
------------------------------------------------------------------------

module Agda.Interaction.Response
  ( Response (..)
  , RemoveTokenBasedHighlighting (..)
  , MakeCaseVariant (..)
  , DisplayInfo (..)
  , Status (..)
  , GiveResult (..)
  , InteractionOutputCallback
  , defaultInteractionOutputCallback
  ) where

import Agda.Interaction.Highlighting.Precise
import {-# SOURCE #-} Agda.TypeChecking.Monad.Base
import Agda.Syntax.Common   (InteractionId(..))
import Agda.Syntax.Concrete (Expr)
import Agda.Utils.Pretty

import Control.Monad.Trans
import Data.Int
import System.IO

#include "undefined.h"
import Agda.Utils.Impossible

-- | Responses for any interactive interface
--
--   Note that the response is given in pieces and incrementally,
--   so the user can have timely response even during long computations.

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
      -- ^ A command sent when an abort command has completed
      -- successfully.

-- | Should token-based highlighting be removed in conjunction with
-- the application of new highlighting (in order to reduce the risk of
-- flicker)?

data RemoveTokenBasedHighlighting
  = RemoveHighlighting
    -- ^ Yes, remove all token-based highlighting from the file.
  | KeepHighlighting
    -- ^ No.

-- | There are two kinds of \"make case\" commands.

data MakeCaseVariant = Function | ExtendedLambda

-- | Info to display at the end of an interactive command

data DisplayInfo
    = Info_CompilationOk String String
      -- ^ Strings are the warnings and the (non-fatal) errors
    | Info_Constraints String
    | Info_AllGoalsWarnings String String String
        -- ^ Strings are the goals, the warnings and the (non-fatal) errors
    | Info_Time Doc
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
    | Info_SearchAbout Doc
    | Info_WhyInScope Doc
    | Info_NormalForm Doc
    | Info_GoalType Doc
    | Info_CurrentGoal Doc
    | Info_InferredType Doc
    | Info_Context Doc
    | Info_HelperFunction Doc
    | Info_Version
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

-- | The default 'InteractionOutputCallback' function prints certain
-- things to stdout (other things generate internal errors).

defaultInteractionOutputCallback :: InteractionOutputCallback
defaultInteractionOutputCallback r = case r of
  Resp_HighlightingInfo {}  -> __IMPOSSIBLE__
  Resp_Status {}            -> __IMPOSSIBLE__
  Resp_JumpToError {}       -> __IMPOSSIBLE__
  Resp_InteractionPoints {} -> __IMPOSSIBLE__
  Resp_GiveAction {}        -> __IMPOSSIBLE__
  Resp_MakeCase {}          -> __IMPOSSIBLE__
  Resp_SolveAll {}          -> __IMPOSSIBLE__
  Resp_DisplayInfo {}       -> __IMPOSSIBLE__
  Resp_RunningInfo _ s      -> liftIO $ do
                                 putStr s
                                 hFlush stdout
  Resp_ClearRunningInfo {}  -> __IMPOSSIBLE__
  Resp_ClearHighlighting {} -> __IMPOSSIBLE__
  Resp_DoneAborting {}      -> __IMPOSSIBLE__
