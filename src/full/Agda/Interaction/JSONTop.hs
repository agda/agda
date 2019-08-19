module Agda.Interaction.JSONTop
    ( jsonREPL
    ) where
import Control.Monad.State

import Data.Aeson hiding (Result(..))
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BS

import Agda.Interaction.AgdaTop
import Agda.Interaction.Response as R
import Agda.Interaction.Highlighting.JSON
import Agda.Syntax.Common
import Agda.TypeChecking.Monad

----------------------------------

-- | 'jsonREPL' is a interpreter like 'mimicGHCi', but outputs JSON-encoded strings.
--
--   'jsonREPL' reads Haskell values (that starts from 'IOTCM' ...) from stdin,
--   interprets them, and outputs JSON-encoded strings. into stdout.

jsonREPL :: TCM () -> TCM ()
jsonREPL = repl (liftIO . BS.putStrLn <=< liftIO . jsonifyResponse) "JSON> "

instance ToJSON Status where
  toJSON status = object
    [ "showImplicitArguments" .= sShowImplicitArguments status
    , "checked" .= sChecked status
    ]

instance ToJSON InteractionId where
  toJSON (InteractionId i) = toJSON i

instance ToJSON GiveResult where
  toJSON (Give_String s) = toJSON s
  toJSON Give_Paren = toJSON True
  toJSON Give_NoParen = toJSON False

instance ToJSON MakeCaseVariant where
  toJSON R.Function = String "Function"
  toJSON R.ExtendedLambda = String "ExtendedLambda"

-- we leave some of the fields as Null for the moment
instance ToJSON DisplayInfo where
  toJSON _ = Null
  -- toJSON (Info_CompilationOk warningsAndErrors) = object
  --   [ "kind"        .= String "CompilationOk"
  --   , "warnings"    .= Null
  --   , "errors"      .= Null
  --   ]
  -- toJSON (Info_Constraints constraints) = object
  --   [ "kind"        .= String "Constraints"
  --   , "constraints" .= Null
  --   ]
  -- toJSON (Info_AllGoalsWarnings _goals _warningsAndErrors) = object
  --   [ "kind"        .= String "AllGoalsWarnings"
  --   , "goals"       .= Null
  --   , "warnings"    .= Null
  --   , "errors"      .= Null
  --   ]
  -- toJSON (Info_Time doc) = object
  --   [ "kind"        .= String "Time"
  --   , "payload"     .= Null
  --   ]
  -- toJSON (Info_Error msg) = object
  --   [ "kind"        .= String "Error"
  --   , "payload"     .= Null
  --   ]
  -- toJSON Info_Intro_NotFound = object
  --   [ "kind"        .= String "IntroNotFound"
  --   , "payload"     .= Null
  --   ]
  -- toJSON (Info_Intro_ConstructorUnknown introductions) = object
  --   [ "kind"        .= String "IntroConstructorUnknown"
  --   , "payload"     .= Null
  --   ]
  -- toJSON (Info_Auto _) = object
  --   [ "kind"        .= String "Auto"
  --   , "payload"     .= Null
  --   ]
  -- toJSON (Info_ModuleContents _ _ _) = object
  --   [ "kind"        .= String "ModuleContents"
  --   , "payload"     .= Null
  --   ]
  -- toJSON (Info_SearchAbout _ _) = object
  --   [ "kind"        .= String "SearchAbout"
  --   , "payload"     .= Null
  --   ]
  -- toJSON (Info_WhyInScope _ _ _ _ _) = object
  --   [ "kind"        .= String "WhyInScope"
  --   , "payload"     .= Null
  --   ]
  -- toJSON (Info_NormalForm _) = object
  --   [ "kind"        .= String "NormalForm"
  --   , "payload"     .= Null
  --   ]
  -- toJSON (Info_NormalForm _ _) = object
  --   [ "kind"        .= String "NormalForm"
  --   , "payload"     .= Null
  --   ]
  -- toJSON (Info_GoalType doc) = object [ "kind" .= String "GoalType", "payload" .= render doc ]
  -- toJSON (Info_CurrentGoal doc) = object [ "kind" .= String "CurrentGoal", "payload" .= render doc ]
  -- toJSON (Info_InferredType doc) = object [ "kind" .= String "InferredType", "payload" .= render doc ]
  -- toJSON (Info_Context ii doc) = object [ "kind" .= String "Context", "payload" .= render doc ]
  -- toJSON (Info_HelperFunction doc) = object [ "kind" .= String "HelperFunction", "payload" .= render doc ]
  -- toJSON Info_Version = object
  --   [ "kind" .= String "Version"
  --   , "version" .= (("Agda version " ++ versionWithCommitInfo) :: String)
  --   ]

-- | Convert Response to an JSON value for interactive editor frontends.
jsonifyResponse :: Response -> IO ByteString
jsonifyResponse (Resp_HighlightingInfo info remove method modFile) =
   encode <$> jsonifyHighlightingInfo info remove method modFile
jsonifyResponse (Resp_DisplayInfo info) = return $ encode $ object
  [ "kind" .= String "DisplayInfo"
  , "info" .= info
  ]
jsonifyResponse (Resp_ClearHighlighting tokenBased) = return $ encode $ object
  [ "kind"          .= String "ClearHighlighting"
  , "tokenBased"    .= tokenBased
  ]
jsonifyResponse Resp_DoneAborting = return $ encode $ object [ "kind" .= String "DoneAborting" ]
jsonifyResponse Resp_ClearRunningInfo = return $ encode $ object [ "kind" .= String "ClearRunningInfo" ]
jsonifyResponse (Resp_RunningInfo debugLevel msg) = return $ encode $ object
  [ "kind"          .= String "RunningInfo"
  , "debugLevel"    .= debugLevel
  , "message"       .= msg
  ]
jsonifyResponse (Resp_Status status) = return $ encode $ object
  [ "kind"          .= String "Status"
  , "status"        .= status
  ]
jsonifyResponse (Resp_JumpToError filepath position) = return $ encode $ object
  [ "kind"          .= String "JumpToError"
  , "filepath"      .= filepath
  , "position"      .= position
  ]
jsonifyResponse (Resp_InteractionPoints interactionPoints) = return $ encode $ object
  [ "kind"              .= String "InteractionPoints"
  , "interactionPoints" .= interactionPoints
  ]
jsonifyResponse (Resp_GiveAction i giveResult) = return $ encode $ object
  [ "kind"              .= String "GiveAction"
  , "interactionPoint"  .= i
  , "giveResult"        .= giveResult
  ]
jsonifyResponse (Resp_MakeCase i variant clauses) = return $ encode $ object
  [ "kind"          .= String "MakeCase"
  , "interactionPoint"  .= i
  , "variant"       .= variant
  , "clauses"       .= clauses
  ]
jsonifyResponse (Resp_SolveAll solutions) = return $ encode $ object
  [ "kind"          .= String "SolveAll"
  , "solutions"     .= map encodeSolution solutions
  ]
  where
    encodeSolution (i, expr) = object
      [ "interactionPoint"  .= i
      , "expression"        .= show expr
      ]
