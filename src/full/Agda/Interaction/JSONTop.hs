module Agda.Interaction.JSONTop
    ( jsonREPL
    ) where
import Control.Monad.State

import Data.Aeson hiding (Result(..))
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Text as T

import Agda.Interaction.AgdaTop
import Agda.Interaction.Base (CommandState(..))
import Agda.Interaction.BasicOps (ComputeMode(..), Rewrite(..))
import Agda.Interaction.JSON
import Agda.Interaction.Response as R
import Agda.Interaction.Highlighting.JSON
import Agda.Syntax.Common
import Agda.Syntax.Concrete.Name (NameInScope(..))
import Agda.TypeChecking.Monad hiding (NotInScope)
import Agda.VersionCommit

import Agda.TypeChecking.Pretty (PrettyTCM(..), prettyTCM)
-- borrowed from EmacsTop, for temporarily serialising stuff
import Agda.TypeChecking.Pretty.Warning (prettyTCWarnings, prettyTCWarnings')
import Agda.TypeChecking.Warnings (WarningsAndNonFatalErrors(..))
import Agda.Utils.Pretty (Pretty(..), render)
import Agda.Utils.Time (CPUTime(..))

--------------------------------------------------------------------------------

-- | 'jsonREPL' is a interpreter like 'mimicGHCi', but outputs JSON-encoded strings.
--
--   'jsonREPL' reads Haskell values (that starts from 'IOTCM' ...) from stdin,
--   interprets them, and outputs JSON-encoded strings. into stdout.

jsonREPL :: TCM () -> TCM ()
jsonREPL = repl (liftIO . BS.putStrLn <=< jsonifyResponse) "JSON> "

instance EncodeTCM NameInScope where
instance ToJSON NameInScope where
  toJSON InScope    = Bool True
  toJSON NotInScope = Bool False

instance EncodeTCM Status where
instance ToJSON Status where
  toJSON status = object
    [ "showImplicitArguments" .= sShowImplicitArguments status
    , "checked"               .= sChecked status
    ]

instance EncodeTCM CommandState where
instance ToJSON CommandState where
  toJSON commandState = object
    [ "interactionPoints" .= theInteractionPoints commandState
    -- more?
    ]

instance EncodeTCM ResponseContextEntry where
  encodeTCM entry = obj
    [ "originalName" @= encodePretty (respOrigName entry)
    , "reifiedName"  @= encodePretty (respReifName entry)
    , "binding"      #= encodePrettyTCM (respType entry)
    , "inScope"      @= respInScope entry
    ]

instance EncodeTCM InteractionId where
instance ToJSON InteractionId where
  toJSON (InteractionId i) = toJSON i

instance EncodeTCM GiveResult where
instance ToJSON GiveResult where
  toJSON (Give_String s) = object [ "str" .= s ]
  toJSON Give_Paren   = object [ "paren" .= Bool True ]
  toJSON Give_NoParen = object [ "paren" .= Bool False ]

instance EncodeTCM MakeCaseVariant where
instance ToJSON MakeCaseVariant where
  toJSON R.Function = String "Function"
  toJSON R.ExtendedLambda = String "ExtendedLambda"

encodePretty :: Pretty a => a -> Value
encodePretty = encodeShow . pretty

encodeShow :: Show a => a -> Value
encodeShow = String . T.pack . show

encodePrettyTCM :: PrettyTCM a => a -> TCM Value
encodePrettyTCM = (encodeShow <$>) . prettyTCM

instance EncodeTCM Rewrite where
instance ToJSON Rewrite where toJSON = encodeShow

instance EncodeTCM CPUTime where
instance ToJSON CPUTime where toJSON = encodePretty

instance EncodeTCM ComputeMode where
instance ToJSON ComputeMode where toJSON = encodeShow

instance EncodeTCM DisplayInfo where
  encodeTCM (Info_CompilationOk wes) = kind "CompilationOk"
    [ "warnings"          #= prettyTCWarnings (tcWarnings wes)
    , "errors"            #= prettyTCWarnings (nonFatalErrors wes)
    ]
  encodeTCM (Info_Constraints constraints) = kind "Constraints"
    [ "constraints"       @= Null
    ]
  encodeTCM (Info_AllGoalsWarnings _goals wes) = kind "AllGoalsWarnings"
    [ "goals"             @= Null
    , "warnings"          #= prettyTCWarnings (tcWarnings wes)
    , "errors"            #= prettyTCWarnings (nonFatalErrors wes)
    ]
  encodeTCM (Info_Time time) = kind "Time"
    [ "time"              @= time
    ]
  encodeTCM (Info_Error msg) = kind "Error"
    [ "payload"           @= Null
    ]
  encodeTCM Info_Intro_NotFound = kind "IntroNotFound"
    [ "payload"           @= Null
    ]
  encodeTCM (Info_Intro_ConstructorUnknown introductions) = kind "IntroConstructorUnknown"
    [ "payload"           @= Null
    ]
  encodeTCM (Info_Auto info) = kind "Auto"
    [ "info"              @= toJSON info
    ]
  encodeTCM (Info_ModuleContents _ _ _) = kind "ModuleContents"
    [ "payload"           @= Null
    ]
  encodeTCM (Info_SearchAbout _ search) = kind "SearchAbout"
    [ "payload"           @= Null
    , "search"            @= toJSON search
    ]
  encodeTCM (Info_WhyInScope _ _ _ _ _) = kind "WhyInScope"
    [ "payload"           @= Null
    ]
  encodeTCM (Info_NormalForm commandState computeMode time expr) = kind "NormalForm"
    [ "commandState"      @= commandState
    , "computeMode"       @= computeMode
    , "time"              @= time
    , "expr"              #= encodePrettyTCM expr
    ]
  encodeTCM (Info_InferredType commandState time expr) = kind "InferredType"
    [ "commandState"      @= commandState
    , "time"              @= time
    , "expr"              #= encodePrettyTCM expr
    ]
  encodeTCM (Info_Context ii ctx) = kind "Context"
    [ "interactionPoint"  @= ii
    , "context"           @= ctx
    ]
  encodeTCM Info_Version = kind "Version"
    [ "version"           @= (versionWithCommitInfo :: String)
    ]
  encodeTCM (Info_GoalSpecific ii info) = kind "GoalSpecific"
    [ "interactionPoint"  @= ii
    , "goalInfo"          @= info
    ]

instance EncodeTCM GoalTypeAux where
  encodeTCM GoalOnly = kind "GoalOnly" []
  encodeTCM (GoalAndHave expr) = kind "GoalAndHave"
    [ "expr" #= encodePrettyTCM expr ]
  encodeTCM (GoalAndElaboration term) = kind "GoalAndElaboration"
    [ "term" #= encodePrettyTCM term ]

instance EncodeTCM GoalDisplayInfo where
  encodeTCM (Goal_HelperFunction payload) = kind "HelperFunction"
    [ "payload"     @= Null -- render payload
    ]
  encodeTCM (Goal_NormalForm computeMode expr) = kind "NormalForm"
    [ "computeMode" @= computeMode
    , "expr"        #= encodePrettyTCM expr
    ]
  encodeTCM (Goal_GoalType rewrite goalType entries outputForms) = kind "GoalType"
    [ "rewrite"     @= rewrite
    , "type"        @= goalType
    , "entries"     @= entries
    , "outputForms" @= Null -- render outputForms
    ]
  encodeTCM (Goal_CurrentGoal rewrite) = kind "CurrentGoal"
    [ "rewrite"     @= rewrite
    ]
  encodeTCM (Goal_InferredType expr) = kind "InferredType"
    [ "expr"        #= encodePrettyTCM expr
    ]

instance EncodeTCM Response where
  encodeTCM (Resp_HighlightingInfo info remove method modFile) =
    liftIO $ jsonifyHighlightingInfo info remove method modFile
  encodeTCM (Resp_DisplayInfo info) = kind "DisplayInfo"
    [ "info"          @= info
    ]
  encodeTCM (Resp_ClearHighlighting tokenBased) = kind "ClearHighlighting"
    [ "tokenBased"    @= tokenBased
    ]
  encodeTCM Resp_DoneAborting = kind "DoneAborting" []
  encodeTCM Resp_ClearRunningInfo = kind "ClearRunningInfo" []
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
  encodeTCM (Resp_MakeCase id variant clauses) = kind "MakeCase"
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
jsonifyResponse = pure . encode <=< encodeTCM
