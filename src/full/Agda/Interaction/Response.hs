------------------------------------------------------------------------
-- | Data type for all interactive responses
------------------------------------------------------------------------

module Agda.Interaction.Response
  ( Response (..)
  , RemoveTokenBasedHighlighting (..)
  , MakeCaseVariant (..)
  , DisplayInfo (..)
  , GoalDisplayInfo(..)
  , Goals
  , WarningsAndNonFatalErrors
  , Info_Error(..)
  , GoalTypeAux(..)
  , ResponseContextEntry(..)
  , Status (..)
  , GiveResult (..)
  , InteractionOutputCallback
  , defaultInteractionOutputCallback
  ) where

import {-# SOURCE #-} Agda.Interaction.BasicOps
  (OutputForm, ComputeMode, Rewrite, OutputConstraint, OutputConstraint')
import Agda.Interaction.Base (CommandState)
import Agda.Interaction.Highlighting.Precise
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common   (InteractionId(..), Arg)
import Agda.Syntax.Concrete (Expr, Name)
import Agda.Syntax.Concrete.Name (NameInScope)
import Agda.Syntax.Scope.Base (AbstractModule, AbstractName, LocalVar)
import qualified Agda.Syntax.Internal as I
import {-# SOURCE #-} Agda.TypeChecking.Monad.Base
  (TCM, TCErr, TCWarning, HighlightingMethod, ModuleToSource, NamedMeta, TCWarning)
import Agda.TypeChecking.Warnings (WarningsAndNonFatalErrors)
import Agda.Utils.Impossible
import Agda.Utils.Time

import Control.Monad.Trans
import Data.Int
import System.IO

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
    | Resp_MakeCase InteractionId MakeCaseVariant [String]
      -- ^ Response is list of printed clauses.
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
    = Info_CompilationOk WarningsAndNonFatalErrors
    | Info_Constraints [OutputForm Expr Expr]
    | Info_AllGoalsWarnings Goals WarningsAndNonFatalErrors
    | Info_Time CPUTime
    | Info_Error Info_Error
        -- ^ When an error message is displayed this constructor should be
        -- used, if appropriate.
    | Info_Intro_NotFound
    | Info_Intro_ConstructorUnknown [String]
    | Info_Auto String
        -- ^ 'Info_Auto' denotes either an error or a success (when 'Resp_GiveAction' is present)
        --   TODO: split these into separate constructors
    | Info_ModuleContents [Name] I.Telescope [(Name, I.Type)]
    | Info_SearchAbout [(Name, I.Type)] String
    | Info_WhyInScope String FilePath (Maybe LocalVar) [AbstractName] [AbstractModule]
    | Info_NormalForm CommandState ComputeMode (Maybe CPUTime) A.Expr
    | Info_InferredType CommandState (Maybe CPUTime) A.Expr
    | Info_Context InteractionId [ResponseContextEntry]
    | Info_Version
    | Info_GoalSpecific InteractionId GoalDisplayInfo

data GoalDisplayInfo
    = Goal_HelperFunction (OutputConstraint' A.Expr A.Expr)
    | Goal_NormalForm ComputeMode A.Expr
    | Goal_GoalType Rewrite GoalTypeAux [ResponseContextEntry] [OutputForm Expr Expr]
    | Goal_CurrentGoal Rewrite
    | Goal_InferredType A.Expr

-- | Goals & Warnings
type Goals = ( [OutputConstraint A.Expr InteractionId] -- visible metas
             , [OutputConstraint A.Expr NamedMeta]     -- hidden metas
             )

-- | Errors that goes into Info_Error
--
--   When an error message is displayed this constructor should be
--   used, if appropriate.
data Info_Error
    = Info_GenericError TCErr
    | Info_CompilationError [TCWarning]
    | Info_HighlightingParseError InteractionId
    | Info_HighlightingScopeCheckError InteractionId

-- | Auxiliary information that comes with Goal Type

data GoalTypeAux
    = GoalOnly
    | GoalAndHave A.Expr
    | GoalAndElaboration I.Term

-- | Entry in context.

data ResponseContextEntry = ResponseContextEntry
  { respOrigName :: Name        -- ^ The original concrete name.
  , respReifName :: Name        -- ^ The name reified from abstract syntax.
  , respType     :: Arg A.Expr  -- ^ The type.
  , respInScope  :: NameInScope -- ^ Whether the 'respReifName' is in scope.
  }


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
