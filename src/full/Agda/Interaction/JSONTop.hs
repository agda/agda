{-# LANGUAGE OverloadedStrings #-}

module Agda.Interaction.JSONTop
    ( jsonREPL
    ) where
import Control.Monad.State

import Data.Aeson hiding (Result(..))
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BS

import Agda.Interaction.AgdaTop
import Agda.Interaction.BasicOps
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
  encodeTCM (Info_AllGoalsWarnings (AllGoalsWarnings ims hms ws es) _ _ _) = obj
    [ "kind"              @= String "AllGoalsWarnings"
    , "interactionMetas"  @= ims
    , "hiddenMetas"       @= hms
    , "warnings"          #= mapM encodeTCM ws
    , "errors"            #= mapM encodeTCM es
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

instance EncodeTCM GiveResult where
instance ToJSON GiveResult where
  toJSON (Give_String s)  = toJSON s
  toJSON Give_Paren       = toJSON True
  toJSON Give_NoParen     = toJSON False

instance EncodeTCM MakeCaseVariant where
instance ToJSON MakeCaseVariant where
  toJSON R.Function       = String "Function"
  toJSON R.ExtendedLambda = String "ExtendedLambda"

--------------------------------------------------------------------------------

instance (EncodeTCM a, EncodeTCM b, ToJSON a, ToJSON b) => EncodeTCM (OutputConstraint a b) where
instance (ToJSON a, ToJSON b) => ToJSON (OutputConstraint a b) where
  toJSON o = case o of
    OfType e t -> object
      [ "kind"        .= String "OfType"
      , "term"        .= e
      , "type"        .= t
      ]
    CmpInType cmp t e e' -> object
      [ "kind"        .= String "CmpInType"
      , "comparison"  .= cmp
      , "term1"       .= e
      , "term2"       .= e'
      , "type"        .= t
      ]
    CmpElim _ t es es' -> object
      [ "kind"        .= String "CmpElim"
      , "terms1"      .= es
      , "terms2"      .= es'
      , "type"        .= t
      ]
    JustType t -> object
      [ "kind"        .= String "JustType"
      , "type"        .= t
      ]
    CmpTypes cmp t t' -> object
      [ "kind"        .= String "CmpTypes"
      , "comparison"  .= cmp
      , "type1"       .= t
      , "type2"       .= t'
      ]
    CmpLevels cmp t t' -> object
      [ "kind"        .= String "CmpLevels"
      , "comparison"  .= cmp
      , "type1"       .= t
      , "type2"       .= t'
      ]
    CmpTeles cmp t t' -> object
      [ "kind"        .= String "CmpTeles"
      , "comparison"  .= cmp
      , "tele1"       .= t
      , "tele2"       .= t'
      ]
    JustSort s -> object
      [ "kind"        .= String "JustSort"
      , "sort"        .= s
      ]
    CmpSorts cmp s s' -> object
      [ "kind"        .= String "CmpSorts"
      , "comparison"  .= cmp
      , "sort1"       .= s
      , "sort2"       .= s'
      ]
    Guard o pid -> object
      [ "kind"              .= String "Guard"
      , "outputConstraint"  .= o
      , "problemId"         .= pid
      ]
    Assign lhs rhs -> object
      [ "kind"        .= String "Assign"
      , "LHS"         .= lhs
      , "RHS"         .= rhs
      ]
    TypedAssign lhs rhs t -> object
      [ "kind"        .= String "TypedAssign"
      , "type"        .= t
      , "LHS"         .= lhs
      , "RHS"         .= rhs
      ]
    PostponedCheckArgs lhs es t0 t1 -> object
      [ "kind"        .= String "PostponedCheckArgs"
      , "type1"       .= t0
      , "type2"       .= t1
      , "exprs"       .= es
      , "LHS"         .= lhs
      ]
    IsEmptyType t -> object
      [ "kind"        .= String "IsEmptyType"
      , "type"        .= t
      ]
    SizeLtSat s -> object
      [ "kind"        .= String "SizeLtSat"
      , "size"        .= s
      ]
    FindInScopeOF e t cs -> object
      [ "kind"        .= String "FindInScopeOF"
      , "term"        .= e
      , "type"        .= t
      , "candidates"  .= cs
      ]
    PTSInstance a b -> object
      [ "kind"        .= String "PTSInstance"
      , "a"           .= a
      , "b"           .= b
      ]
