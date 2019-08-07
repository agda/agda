module Agda.Interaction.JSONTop
    ( jsonREPL
    ) where
import Control.Monad.State

import Data.Aeson hiding (Result(..))
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BS

import Agda.Interaction.AgdaTop
import Agda.Interaction.JSON.Encode
import Agda.Interaction.Response as R
import Agda.Interaction.Highlighting.JSON
import Agda.Syntax.Common
import Agda.TypeChecking.Monad
import Agda.VersionCommit

-- borrowed from EmacsTop, for temporarily serialising stuff
import Agda.TypeChecking.Pretty.Warning (prettyTCWarnings, prettyTCWarnings')
import Agda.TypeChecking.Warnings (WarningsAndNonFatalErrors(..))
import Agda.Utils.Pretty (render)

--------------------------------------------------------------------------------

-- | 'jsonREPL' is a interpreter like 'mimicGHCi', but outputs JSON-encoded strings.
--
--   'jsonREPL' reads Haskell values (that starts from 'IOTCM' ...) from stdin,
--   interprets them, and outputs JSON-encoded strings. into stdout.

jsonREPL :: TCM () -> TCM ()
jsonREPL = repl (liftIO . BS.putStrLn <=< jsonifyResponse) "JSON> "

instance EncodeTCM Status where
instance ToJSON Status where
  toJSON status = object
    [ "showImplicitArguments" .= sShowImplicitArguments status
    , "checked" .= sChecked status
    ]

instance EncodeTCM InteractionId where
instance ToJSON InteractionId where
  toJSON (InteractionId i) = toJSON i

instance EncodeTCM GiveResult where
instance ToJSON GiveResult where
  toJSON (Give_String s) = toJSON s
  toJSON Give_Paren = toJSON True
  toJSON Give_NoParen = toJSON False

instance EncodeTCM MakeCaseVariant where
instance ToJSON MakeCaseVariant where
  toJSON R.Function = String "Function"
  toJSON R.ExtendedLambda = String "ExtendedLambda"

instance EncodeTCM DisplayInfo where
  encodeTCM (Info_CompilationOk wes) = kind "CompilationOk"
    [ "warnings"    #= prettyTCWarnings (tcWarnings wes)
    , "errors"      #= prettyTCWarnings (nonFatalErrors wes)
    ]
  encodeTCM (Info_Constraints constraints) = kind "Constraints"
    [ "constraints" @= Null
    ]
  encodeTCM (Info_AllGoalsWarnings _goals _warningsAndErrors) = kind "AllGoalsWarnings"
    [ "goals"       @= Null
    , "warnings"    @= Null
    , "errors"      @= Null
    ]
  encodeTCM (Info_Time doc) = kind "Time"
    [ "payload"     @= Null
    ]
  encodeTCM (Info_Error msg) = kind "Error"
    [ "payload"     @= Null
    ]
  encodeTCM Info_Intro_NotFound = kind "IntroNotFound"
    [ "payload"     @= Null
    ]
  encodeTCM (Info_Intro_ConstructorUnknown introductions) = kind "IntroConstructorUnknown"
    [ "payload"     @= Null
    ]
  encodeTCM (Info_Auto _) = kind "Auto"
    [ "payload"     @= Null
    ]
  encodeTCM (Info_ModuleContents _ _ _) = kind "ModuleContents"
    [ "payload"     @= Null
    ]
  encodeTCM (Info_SearchAbout _ _) = kind "SearchAbout"
    [ "payload"     @= Null
    ]
  encodeTCM (Info_WhyInScope _ _ _ _ _) = kind "WhyInScope"
    [ "payload"     @= Null
    ]
  encodeTCM (Info_NormalForm commandState computeMode time expr) = kind "NormalForm"
    [ "commandState"  @= Null
    , "computeMode"   @= Null
    , "time"          @= Null
    , "expr"          @= Null
    ]
  encodeTCM (Info_InferredType commandState time expr) = kind "InferredType"
    [ "commandState"  @= Null
    , "time"          @= Null
    , "expr"          @= Null
    ]
  encodeTCM (Info_Context ii doc) = kind "Context"
    [ "payload"     @= Null -- render doc
    ]
  encodeTCM Info_Version = kind "Version"
    [ "version"     @= (("Agda version " ++ versionWithCommitInfo) :: String)
    ]
  encodeTCM (Info_GoalSpecific ii info) = kind "GoalSpecific"
    [ "interactionPoint"  @= Null -- render ii
    , "payload"           @= Null -- render info
    ]

instance ToJSON GoalDisplayInfo where
  toJSON (Goal_HelperFunction payload) = object
    [ "kind"        .= String "HelperFunction"
    , "payload"     .= Null -- render payload
    ]
  toJSON (Goal_NormalForm computeMode expr) = object
    [ "kind"        .= String "NormalForm"
    , "computeMode" .= Null -- render computeMode
    , "expr"        .= Null -- render expr
    ]
  toJSON (Goal_GoalType rewrite goalType entries outputForms) = object
    [ "kind"        .= String "GoalType"
    , "rewrite"     .= Null -- render rewrite
    , "type"        .= Null -- render goalType
    , "entries"     .= Null -- render entries
    , "outputForms" .= Null -- render outputForms
    ]
  toJSON (Goal_CurrentGoal rewrite) = object
    [ "kind"        .= String "CurrentGoal"
    , "rewrite"     .= Null -- render rewrite
    ]
  toJSON (Goal_InferredType expr) = object
    [ "kind"        .= String "InferredType"
    , "expr"        .= Null -- render expr
    ]

instance EncodeTCM Response where
  encodeTCM (Resp_HighlightingInfo info remove method modFile) =
    liftIO $ jsonifyHighlightingInfo info remove method modFile
  encodeTCM (Resp_DisplayInfo info) = kind "DisplayInfo"
    [ "info" @= info
    ]
  encodeTCM (Resp_ClearHighlighting tokenBased) = kind "ClearHighlighting"
    [ "tokenBased"    @= tokenBased
    ]
  encodeTCM Resp_DoneAborting = kind "DoneAborting"
    []
  encodeTCM Resp_ClearRunningInfo = kind "ClearRunningInfo"
    []
  encodeTCM (Resp_RunningInfo debugLevel msg) = kind "RunningInfo"
    [ "debugLevel"    @= debugLevel
    , "message"       @= msg
    ]
  encodeTCM (Resp_Status status) = kind "Status"
    [ "status"        @= status
    ]
  encodeTCM (Resp_JumpToError filepath position) = kind "JumpToError"
    [ "filepath"      @= filepath
    , "position"      @= position
    ]
  encodeTCM (Resp_InteractionPoints interactionPoints) = kind "InteractionPoints"
    [ "interactionPoints" @= interactionPoints
    ]
  encodeTCM (Resp_GiveAction i giveResult) = kind "GiveAction"
    [ "interactionPoint"  @= i
    , "giveResult"        @= giveResult
    ]
  encodeTCM (Resp_MakeCase variant clauses) = kind "MakeCase"
    [ "variant"       @= variant
    , "clauses"       @= clauses
    ]
  encodeTCM (Resp_SolveAll solutions) = kind "SolveAll"
    [ "solutions"     @= map encodeSolution solutions
    ]
    where
      encodeSolution (i, expr) = object
        [ "interactionPoint"  .= i
        , "expression"        .= show expr
        ]

-- | Convert Response to an JSON value for interactive editor frontends.
jsonifyResponse :: Response -> TCM ByteString
jsonifyResponse = return . encode <=< encodeTCM
