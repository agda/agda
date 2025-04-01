------------------------------------------------------------------------
-- | Data type for all interactive responses
------------------------------------------------------------------------

module Agda.Interaction.Response.Base
  ( Response_boot (..)
  , RemoveTokenBasedHighlighting (..)
  , MakeCaseVariant (..)
  , DisplayInfo_boot (..)
  , GoalDisplayInfo_boot(..)
  , Goals_boot
  , Info_Error_boot(..)
  , GoalTypeAux(..)
  , ResponseContextEntry(..)
  , Status (..)
  , GiveResult (..)
  ) where

import Control.Monad.Trans ( MonadIO(liftIO) )
import Data.Set (Set)
import Data.Word (Word32)

import Agda.Interaction.Base
  ( CommandState
  , CompilerBackend
  , ComputeMode
  , OutputConstraint_boot
  , OutputConstraint'
  , OutputForm_boot
  , Rewrite
  )
import Agda.Interaction.Highlighting.Precise
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Common         (InteractionId(..), Arg)
import Agda.Syntax.Concrete       (Expr)
import Agda.Syntax.Concrete.Name  (Name, QName, NameInScope)
import Agda.Syntax.Scope.Base     (WhyInScopeData)
import qualified Agda.Syntax.Internal as I
import Agda.TypeChecking.Monad.Base.Types
  (HighlightingMethod, ModuleToSource, NamedMeta, IPFace')
import Agda.Utils.Impossible
import Agda.Utils.Time

-- | Responses for any interactive interface
--
--   Note that the response is given in pieces and incrementally,
--   so the user can have timely response even during long computations.

data Response_boot tcErr tcWarning warningsAndNonFatalErrors
    = Resp_HighlightingInfo
        HighlightingInfo
        RemoveTokenBasedHighlighting
        HighlightingMethod
        ModuleToSource
    | Resp_Status Status
    | Resp_JumpToError FilePath Word32
    | Resp_InteractionPoints [InteractionId]
    | Resp_GiveAction InteractionId GiveResult
    | Resp_MakeCase InteractionId MakeCaseVariant [String]
      -- ^ Response is list of printed clauses.
    | Resp_SolveAll [(InteractionId, Expr)]
      -- ^ Solution for one or more meta-variables.
    | Resp_Mimer InteractionId (Maybe String)
    | Resp_DisplayInfo (DisplayInfo_boot tcErr tcWarning warningsAndNonFatalErrors)
    | Resp_RunningInfo Int String
      -- ^ The integer is the message's debug level.
    | Resp_ClearRunningInfo
    | Resp_ClearHighlighting TokenBased
      -- ^ Clear highlighting of the given kind.
    | Resp_DoneAborting
      -- ^ A command sent when an abort command has completed
      -- successfully.
    | Resp_DoneExiting
      -- ^ A command sent when an exit command is about to be
      -- completed.

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

data DisplayInfo_boot tcErr tcWarning warningsAndNonFatalErrors
    = Info_CompilationOk CompilerBackend warningsAndNonFatalErrors
    | Info_Constraints [OutputForm_boot tcErr Expr Expr]
    | Info_AllGoalsWarnings (Goals_boot tcErr) warningsAndNonFatalErrors
    | Info_Time CPUTime
    | Info_Error (Info_Error_boot tcErr tcWarning)
        -- ^ When an error message is displayed this constructor should be
        -- used, if appropriate.
    | Info_Intro_NotFound
    | Info_Intro_ConstructorUnknown [String]
    | Info_Auto String
        -- ^ 'Info_Auto' denotes either an error or a success (when 'Resp_GiveAction' is present)
        --   TODO: split these into separate constructors
    | Info_ModuleContents [Name] I.Telescope [(Name, I.Type)]
    | Info_SearchAbout [(Name, I.Type)] String
    | Info_WhyInScope WhyInScopeData
    | Info_NormalForm CommandState ComputeMode (Maybe CPUTime) A.Expr
    | Info_InferredType CommandState (Maybe CPUTime) A.Expr
    | Info_Context InteractionId [ResponseContextEntry]
    | Info_Version
    | Info_GoalSpecific InteractionId (GoalDisplayInfo_boot tcErr)

data GoalDisplayInfo_boot tcErr
    = Goal_HelperFunction (OutputConstraint' A.Expr A.Expr)
    | Goal_NormalForm ComputeMode A.Expr
    | Goal_GoalType Rewrite GoalTypeAux [ResponseContextEntry] [IPFace' Expr] [OutputForm_boot tcErr Expr Expr]
    | Goal_CurrentGoal Rewrite
    | Goal_InferredType A.Expr

-- | Goals & Warnings
type Goals_boot tcErr =
    ( [OutputConstraint_boot tcErr A.Expr InteractionId] -- visible metas (goals)
    , [OutputConstraint_boot tcErr A.Expr NamedMeta]     -- hidden (unsolved) metas
    )

-- | Errors that goes into Info_Error
--
--   When an error message is displayed this constructor should be
--   used, if appropriate.
data Info_Error_boot tcErr tcWarning
    = Info_GenericError tcErr
    | Info_CompilationError (Set tcWarning)
    | Info_HighlightingParseError InteractionId
    | Info_HighlightingScopeCheckError InteractionId

-- | Auxiliary information that comes with Goal Type

data GoalTypeAux
    = GoalOnly
    | GoalAndHave A.Expr [IPFace' Expr]
    | GoalAndElaboration A.Expr

-- | Entry in context.

data ResponseContextEntry = ResponseContextEntry
  { respOrigName :: Name        -- ^ The original concrete name.
  , respReifName :: Name        -- ^ The name reified from abstract syntax.
  , respType     :: Arg A.Expr  -- ^ The type.
  , respLetValue :: Maybe A.Expr -- ^ The value (if it is a let-bound variable)
  , respInScope  :: NameInScope -- ^ Whether the 'respReifName' is in scope.
  }


-- | Status information.

data Status = Status
  { sShowImplicitArguments :: Bool
    -- ^ Are implicit arguments displayed?
  , sShowIrrelevantArguments :: Bool
    -- ^ Are irrelevant arguments displayed?
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
