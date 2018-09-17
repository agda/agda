{-# LANGUAGE OverloadedStrings #-}

module Agda.Interaction.JSONTop
    ( jsonREPL
    ) where
import Control.Monad.State

import Data.Aeson hiding (Result(..))
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BS

import Agda.Interaction.AgdaTop
import Agda.Interaction.Highlighting.JSON
import Agda.Interaction.JSON.Encode
import Agda.Interaction.JSON.TypeChecking
import Agda.Interaction.Response as R

import Agda.TypeChecking.Monad (TCM)
import Agda.Utils.Pretty (render)
import Agda.VersionCommit (versionWithCommitInfo)

--------------------------------------------------------------------------------

-- | 'jsonREPL' is a interpreter like 'mimicGHCi', but outputs JSON-encoded strings.
--
--   'jsonREPL' reads Haskell values (that starts from 'IOTCM' ...) from stdin,
--   interprets them, and outputs JSON-encoded strings. into stdout.

jsonREPL :: TCM () -> TCM ()
jsonREPL = repl (liftIO . BS.putStrLn <=< return . encode <=< encodeTCM) "JSON> "

--------------------------------------------------------------------------------

instance EncodeTCM Response where
  encodeTCM (Resp_HighlightingInfo info remove method modFile) =
    liftIO (encodeHighlightingInfo info remove method modFile)
  encodeTCM (Resp_DisplayInfo info) = obj
    [ "kind" @= String "DisplayInfo"
    , "info" #= encodeTCM info
    ]
  encodeTCM (Resp_ClearHighlighting tokenBased) = obj
    [ "kind"          @= String "ClearHighlighting"
    , "tokenBased"    @= tokenBased
    ]
  encodeTCM Resp_DoneAborting = obj
    [ "kind"          @= String "DoneAborting"
    ]
  encodeTCM Resp_ClearRunningInfo = obj
    [ "kind"          @= String "ClearRunningInfo"
    ]
  encodeTCM (Resp_RunningInfo debugLevel msg) = obj
    [ "kind"          @= String "RunningInfo"
    , "debugLevel"    @= debugLevel
    , "message"       @= msg
    ]
  encodeTCM (Resp_Status status) = obj
    [ "kind"                  @= String "Status"
    , "showImplicitArguments" @= sShowImplicitArguments status
    , "checked"               @= sChecked status
    ]
  encodeTCM (Resp_JumpToError filepath position) = obj
    [ "kind"          @= String "JumpToError"
    , "filepath"      @= filepath
    , "position"      @= position
    ]
  encodeTCM (Resp_InteractionPoints interactionPoints) = obj
    [ "kind"              @= String "InteractionPoints"
    , "interactionPoints" @= interactionPoints
    ]
  encodeTCM (Resp_GiveAction i giveResult) = obj
    [ "kind"              @= String "GiveAction"
    , "interactionPoint"  @= i
    , "giveResult"        @= giveResult
    ]
  encodeTCM (Resp_MakeCase variant clauses) = obj
    [ "kind"          @= String "MakeCase"
    , "variant"       @= variant
    , "clauses"       @= clauses
    ]
  encodeTCM (Resp_SolveAll solutions) = obj
    [ "kind"          @= String "SolveAll"
    , "solutions"     @= map encodeSolution solutions
    ]
    where
      encodeSolution (i, expr) = object
        [ "interactionPoint"  .= i
        , "expression"        .= show expr
        ]

--------------------------------------------------------------------------------

instance EncodeTCM DisplayInfo where
  encodeTCM (Info_CompilationOk warnings errors) = obj
    [ "kind"        @= String "CompilationOk"
    , "warnings"    @= warnings
    , "errors"      @= errors
    ]
  encodeTCM (Info_Constraints constraints) = obj
    [ "kind"        @= String "Constraints"
    , "constraints" @= constraints
    ]
  encodeTCM (Info_AllGoalsWarnings _ goals warnings errors) = obj
    [ "kind"        @= String "AllGoalsWarnings"
    , "goals"       @= goals
    , "warnings"    @= warnings
    , "errors"      @= errors
    ]
  encodeTCM (Info_Time doc) = obj
    [ "kind"        @= String "Time"
    , "payload"     @= render doc
    ]
  encodeTCM (Info_Error err msg) = obj
    [ "kind"          @= String "Error"
    , "error"         #= encodeTCM err
    , "emacsMessage"  @= msg
    ]
  encodeTCM (Info_Intro doc) = obj
    [ "kind" @= String "Intro", "payload" @= render doc ]
  encodeTCM (Info_Auto msg) = obj
    [ "kind" @= String "Auto", "payload" @= msg ]
  encodeTCM (Info_ModuleContents doc) = obj
    [ "kind" @= String "ModuleContents", "payload" @= render doc ]
  encodeTCM (Info_SearchAbout doc) = obj
    [ "kind" @= String "SearchAbout", "payload" @= render doc ]
  encodeTCM (Info_WhyInScope doc) = obj
    [ "kind" @= String "WhyInScope", "payload" @= render doc ]
  encodeTCM (Info_NormalForm doc) = obj
    [ "kind" @= String "NormalForm", "payload" @= render doc ]
  encodeTCM (Info_GoalType doc) = obj
    [ "kind" @= String "GoalType", "payload" @= render doc ]
  encodeTCM (Info_CurrentGoal doc) = obj
    [ "kind" @= String "CurrentGoal", "payload" @= render doc ]
  encodeTCM (Info_InferredType doc) = obj
    [ "kind" @= String "InferredType", "payload" @= render doc ]
  encodeTCM (Info_Context doc) = obj
    [ "kind" @= String "Context", "payload" @= render doc ]
  encodeTCM (Info_HelperFunction doc) = obj
    [ "kind" @= String "HelperFunction", "payload" @= render doc ]
  encodeTCM Info_Version = obj
    [ "kind"    @= String "Version"
    , "version" @= (("Agda version " ++ versionWithCommitInfo) :: String)
    ]

--------------------------------------------------------------------------------

instance ToJSON GiveResult where
  toJSON (Give_String s) = toJSON s
  toJSON Give_Paren = toJSON True
  toJSON Give_NoParen = toJSON False

instance ToJSON MakeCaseVariant where
  toJSON R.Function = String "Function"
  toJSON R.ExtendedLambda = String "ExtendedLambda"
