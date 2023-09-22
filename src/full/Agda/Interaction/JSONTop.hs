module Agda.Interaction.JSONTop
    ( jsonREPL
    ) where

import Control.Monad
         ( (<=<), forM )
import Control.Monad.IO.Class
         ( MonadIO(..) )

import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BS
import qualified Data.Text as T
import qualified Data.Set as Set

import Agda.Interaction.AgdaTop
import Agda.Interaction.Base
         ( CommandState(..), CurrentFile(..), ComputeMode(..), Rewrite(..), OutputForm(..), OutputConstraint(..) )
import qualified Agda.Interaction.BasicOps as B
import Agda.Interaction.EmacsTop
import Agda.Interaction.JSON
import Agda.Interaction.Response as R
import Agda.Interaction.Highlighting.JSON

import Agda.Syntax.Abstract.Pretty
         ( prettyATop )
import Agda.Syntax.Common
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Name
         ( NameInScope(..), Name )
import Agda.Syntax.Internal
         ( telToList, Dom'(..), Dom, MetaId(..), ProblemId(..), Blocker(..), alwaysUnblock )
import Agda.Syntax.Position
         ( Range, rangeIntervals, Interval'(..), Position'(..), noRange )
import Agda.Syntax.Scope.Base
         ( WhyInScopeData(..) )

import Agda.TypeChecking.Errors
         ( getAllWarningsOfTCErr )
import Agda.TypeChecking.Monad
         ( Comparison(..), inTopContext, TCM, TCErr, TCWarning, NamedMeta(..), withInteractionId )
import Agda.TypeChecking.Monad.MetaVars
         ( getInteractionRange, getMetaRange, withMetaId )
import Agda.TypeChecking.Pretty
         ( PrettyTCM(..), prettyTCM )
-- borrowed from EmacsTop, for temporarily serialising stuff
import Agda.TypeChecking.Pretty.Warning
         ( filterTCWarnings )
import Agda.TypeChecking.Warnings
         ( WarningsAndNonFatalErrors(..) )

import qualified Agda.Syntax.Common.Pretty as P
import Agda.Syntax.Common.Pretty
         ( Pretty(..), prettyShow )
import Agda.Utils.Time
         ( CPUTime(..) )

import Agda.VersionCommit

--------------------------------------------------------------------------------

-- | 'jsonREPL' is a interpreter like 'mimicGHCi', but outputs JSON-encoded strings.
--
--   'jsonREPL' reads Haskell values (that starts from 'IOTCM' ...) from stdin,
--   interprets them, and outputs JSON-encoded strings. into stdout.

jsonREPL :: TCM () -> TCM ()
jsonREPL = repl (liftIO . BS.putStrLn <=< jsonifyResponse) "JSON> "

instance EncodeTCM NameInScope where
instance ToJSON NameInScope where
  toJSON InScope    = toJSON True
  toJSON NotInScope = toJSON False

instance EncodeTCM Status where
instance ToJSON Status where
  toJSON status = object
    [ "showImplicitArguments"   .= sShowImplicitArguments status
    , "showIrrelevantArguments" .= sShowIrrelevantArguments status
    , "checked"                 .= sChecked status
    ]

instance EncodeTCM CommandState where
instance ToJSON CommandState where
  toJSON commandState = object
    [ "interactionPoints" .= theInteractionPoints commandState
    , "currentFile"       .= theCurrentFile commandState
    -- more?
    ]

instance EncodeTCM CurrentFile where
instance ToJSON CurrentFile where
  toJSON (CurrentFile path _ _ time) = toJSON (path, time)  -- backwards compat.

instance EncodeTCM ResponseContextEntry where
  encodeTCM entry = obj
    [ "originalName" @= encodePretty (respOrigName entry)
    , "reifiedName"  @= encodePretty (respReifName entry)
    , "binding"      #= prettyATop (unArg (respType entry))
    , "inScope"      @= respInScope entry
    ]

instance EncodeTCM (Position' ()) where
instance ToJSON (Position' ()) where
  toJSON p = object
    [ "pos"  .= toJSON (posPos p)
    , "line" .= toJSON (posLine p)
    , "col"  .= toJSON (posCol p)
    ]

instance EncodeTCM Range where
instance ToJSON Range where
  toJSON = toJSON . map prettyInterval . rangeIntervals
    where prettyInterval i = object [ "start" .= iStart i, "end" .= iEnd i ]

instance EncodeTCM ProblemId where
instance EncodeTCM MetaId    where

instance ToJSON ProblemId where toJSON (ProblemId i) = toJSON i

instance ToJSON ModuleNameHash where
  toJSON (ModuleNameHash h) = toJSON h

instance ToJSON MetaId where
  toJSON m = object
    [ "id"     .= toJSON (metaId m)
    , "module" .= toJSON (metaModule m)
    ]

instance EncodeTCM InteractionId where
  encodeTCM ii@(InteractionId i) = obj
    [ "id"    @= toJSON i
    , "range" #= intervalsTCM
    ]
    where
      intervalsTCM = toJSON <$> getInteractionRange ii
instance ToJSON InteractionId where
  toJSON (InteractionId i) = toJSON i

instance EncodeTCM NamedMeta where
  encodeTCM m = obj
    [ "name"  #= nameTCM
    , "range" #= intervalsTCM
    ]
    where
      nameTCM = encodeShow <$> withMetaId (nmid m) (prettyATop m)
      intervalsTCM = toJSON <$> getMetaRange (nmid m)

instance EncodeTCM GiveResult where
instance ToJSON GiveResult where
  toJSON (Give_String s) = object [ "str" .= s ]
  toJSON Give_Paren   = object [ "paren" .= True ]
  toJSON Give_NoParen = object [ "paren" .= False ]

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

encodeOCCmp :: (a -> TCM Value)
  -> Comparison -> a -> a -> T.Text
  -> TCM Value
encodeOCCmp f c i j k = kind k
  [ "comparison"     @= encodeShow c
  , "constraintObjs" #= traverse f [i, j]
  ]

  -- Goals
encodeOC :: (a -> TCM Value)
  -> (b -> TCM Value)
  -> OutputConstraint b a
  -> TCM Value
encodeOC f encPrettyTCM = \case
 OfType i a -> kind "OfType"
  [ "constraintObj" #= f i
  , "type"          #= encPrettyTCM a
  ]
 CmpInType c a i j -> kind "CmpInType"
  [ "comparison"     @= encodeShow c
  , "type"           #= encPrettyTCM a
  , "constraintObjs" #= traverse f [i, j]
  ]
 CmpElim ps a is js -> kind "CmpElim"
  [ "polarities"     @= map encodeShow ps
  , "type"           #= encPrettyTCM a
  , "constraintObjs" #= traverse (traverse f) [is, js]
  ]
 JustType a -> kind "JustType"
  [ "constraintObj"  #= f a
  ]
 JustSort a -> kind "JustSort"
  [ "constraintObj"  #= f a
  ]
 CmpTypes  c i j -> encodeOCCmp f c i j "CmpTypes"
 CmpLevels c i j -> encodeOCCmp f c i j "CmpLevels"
 CmpTeles  c i j -> encodeOCCmp f c i j "CmpTeles"
 CmpSorts  c i j -> encodeOCCmp f c i j "CmpSorts"
 Assign i a -> kind "Assign"
  [ "constraintObj"  #= f i
  , "value"          #= encPrettyTCM a
  ]
 TypedAssign i v t -> kind "TypedAssign"
  [ "constraintObj"  #= f i
  , "value"          #= encPrettyTCM v
  , "type"           #= encPrettyTCM t
  ]
 PostponedCheckArgs i es t0 t1 -> kind "PostponedCheckArgs"
  [ "constraintObj"  #= f i
  , "ofType"         #= encPrettyTCM t0
  , "arguments"      #= forM es encPrettyTCM
  , "type"           #= encPrettyTCM t1
  ]
 IsEmptyType a -> kind "IsEmptyType"
  [ "type"           #= encPrettyTCM a
  ]
 SizeLtSat a -> kind "SizeLtSat"
  [ "type"           #= encPrettyTCM a
  ]
 FindInstanceOF i t cs -> kind "FindInstanceOF"
  [ "constraintObj"  #= f i
  , "candidates"     #= forM cs encodeKVPairs
  , "type"           #= encPrettyTCM t
  ]
  where encodeKVPairs (_, v, t) = obj -- TODO: encode kind
          [ "value"  #= encPrettyTCM v
          , "type"   #= encPrettyTCM t
          ]
 PTSInstance a b -> kind "PTSInstance"
  [ "constraintObjs" #= traverse f [a, b]
  ]
 PostponedCheckFunDef name a err -> kind "PostponedCheckFunDef"
  [ "name"           @= encodePretty name
  , "type"           #= encPrettyTCM a
  , "error"          #= encodeTCM err
  ]
 DataSort q s -> kind "DataSort"
  [ "name"           @= encodePretty q
  , "sort"           #= f s
  ]
 CheckLock t lk -> kind "CheckLock"
  [ "head"           #= f t
  , "lock"           #= f lk
  ]
 UsableAtMod mod t -> kind "UsableAtMod"
  [ "mod"           @= encodePretty mod
  , "term"          #= f t
  ]

encodeNamedPretty :: PrettyTCM a => (Name, a) -> TCM Value
encodeNamedPretty (name, a) = obj
  [ "name" @= encodePretty name
  , "term" #= encodePrettyTCM a
  ]

instance EncodeTCM (OutputForm C.Expr C.Expr) where
  encodeTCM (OutputForm range problems unblock oc) = obj
    [ "range"      @= range
    , "problems"   @= problems
    , "unblocker"  @= unblock
    , "constraint" #= encodeOC (pure . encodePretty) (pure . encodePretty) oc
    ]

instance EncodeTCM Blocker where
  encodeTCM (UnblockOnMeta x)    = kind "UnblockOnMeta" [ "meta" @= x ]
  encodeTCM (UnblockOnProblem p) = kind "UnblockOnProblem" [ "id" @= p ]
  encodeTCM (UnblockOnDef q)     = kind "UnblockOnDef" [ "name" @= encodePretty q ]
  encodeTCM (UnblockOnAll us)    = kind "UnblockOnAll" [ "blockers" @= Set.toList us ]
  encodeTCM (UnblockOnAny us)    = kind "UnblockOnAny" [ "blockers" @= Set.toList us ]

instance EncodeTCM DisplayInfo where
  encodeTCM (Info_CompilationOk backend wes) = kind "CompilationOk"
    [ "backend"           @= encodePretty backend
    , "warnings"          #= encodeTCM (filterTCWarnings (tcWarnings wes))
    , "errors"            #= encodeTCM (filterTCWarnings (nonFatalErrors wes))
    ]
  encodeTCM (Info_Constraints constraints) = kind "Constraints"
    [ "constraints"       #= forM constraints encodeTCM
    ]
  encodeTCM (Info_AllGoalsWarnings (vis, invis) wes) = kind "AllGoalsWarnings"
    [ "visibleGoals"      #= forM vis (\i -> withInteractionId (B.outputFormId $ OutputForm noRange [] alwaysUnblock i) $ encodeOC encodeTCM encodePrettyTCM i)
    , "invisibleGoals"    #= forM invis (encodeOC encodeTCM encodePrettyTCM)
    , "warnings"          #= encodeTCM (filterTCWarnings (tcWarnings wes))
    , "errors"            #= encodeTCM (filterTCWarnings (nonFatalErrors wes))
    ]
  encodeTCM (Info_Time time) = kind "Time"
    [ "time"              @= time
    ]
  encodeTCM (Info_Error err) = encodeTCM err
  encodeTCM Info_Intro_NotFound = kind "IntroNotFound" []
  encodeTCM (Info_Intro_ConstructorUnknown introductions) = kind "IntroConstructorUnknown"
    [ "constructors"      @= map toJSON introductions
    ]
  encodeTCM (Info_Auto info) = kind "Auto"
    [ "info"              @= toJSON info
    ]
  encodeTCM (Info_ModuleContents names tele contents) = kind "ModuleContents"
    [ "contents"          #= forM contents encodeNamedPretty
    , "telescope"         #= forM (telToList tele) encodeDomType
    , "names"             @= map encodePretty names
    ]
    where
      encodeDomType :: PrettyTCM a => Dom (ArgName, a) -> TCM Value
      encodeDomType dom = obj
        [ "dom"       #= encodePrettyTCM (unDom dom)
        , "name"      @= fmap encodePretty (bareNameOf dom)
        , "finite"    @= toJSON (domIsFinite dom)
        , "cohesion"  @= encodeShow (modCohesion . argInfoModality $ domInfo dom)
        , "relevance" @= encodeShow (modRelevance . argInfoModality $ domInfo dom)
        , "hiding"    @= case argInfoHiding $ domInfo dom of
          Instance o -> show o
          o -> show o
        ]
  encodeTCM (Info_SearchAbout results search) = kind "SearchAbout"
    [ "results"           #= forM results encodeNamedPretty
    , "search"            @= toJSON search
    ]
  encodeTCM (Info_WhyInScope why@(WhyInScopeData y path _ _ _)) = kind "WhyInScope"
    [ "thing"             @= prettyShow y
    , "filepath"          @= toJSON path
    -- use Emacs message first
    , "message"           #= explainWhyInScope why
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
    , "goalInfo"          #= withInteractionId ii (encodeGoalSpecific ii info)
    ]

instance EncodeTCM GoalTypeAux where
  encodeTCM GoalOnly = kind "GoalOnly" []
  encodeTCM (GoalAndHave expr _) = kind "GoalAndHave"
    [ "expr" #= encodePrettyTCM expr ]
  encodeTCM (GoalAndElaboration term) = kind "GoalAndElaboration"
    [ "term" #= encodePrettyTCM term ]

encodeGoalSpecific :: InteractionId -> GoalDisplayInfo -> TCM Value
encodeGoalSpecific ii = go
  where
  go (Goal_HelperFunction helperType) = kind "HelperFunction"
    [ "signature"   #= inTopContext (prettyATop helperType)
    ]
  go (Goal_NormalForm computeMode expr) = kind "NormalForm"
    [ "computeMode" @= computeMode
    , "expr"        #= B.showComputed computeMode expr
    ]
  go (Goal_GoalType rewrite goalType entries boundary outputForms) = kind "GoalType"
    [ "rewrite"     @= rewrite
    , "typeAux"     @= goalType
    , "type"        #= prettyTypeOfMeta rewrite ii
    , "entries"     @= entries
    , "boundary"    @= map encodePretty boundary
    , "outputForms" @= map encodePretty outputForms
    ]
  go (Goal_CurrentGoal rewrite) = kind "CurrentGoal"
    [ "rewrite"     @= rewrite
    , "type"        #= prettyTypeOfMeta rewrite ii
    ]
  go (Goal_InferredType expr) = kind "InferredType"
    [ "expr"        #= prettyATop expr
    ]

instance EncodeTCM Info_Error where
  encodeTCM (Info_GenericError err) = kind "Error"
    [ "warnings"          #= (getAllWarningsOfTCErr err
                            >>= encodeTCM . filterTCWarnings)
    , "error"             #= encodeTCM err
    ]
  encodeTCM err = kind "Error"
    [ "warnings"          @= ([] :: [String])
    , "error"             #= obj
      [ "message"           #= showInfoError err
      ]
    ]

instance EncodeTCM TCErr where
  encodeTCM err = obj
    [ "message"     #= encodePrettyTCM err
    ]

instance EncodeTCM TCWarning where
  encodeTCM w = obj
    [ "message"     #= (P.render <$> prettyTCM w)
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
  encodeTCM Resp_DoneExiting = kind "DoneExiting" []
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
    [ "interactionPoint"  @= id
    , "variant"           @= variant
    , "clauses"           @= clauses
    ]
  encodeTCM (Resp_SolveAll solutions) = kind "SolveAll"
    [ "solutions"     @= map encodeSolution solutions
    ]
    where
      encodeSolution (i, expr) = object
        [ "interactionPoint"  .= i
        , "expression"        .= P.prettyShow expr
        ]

-- | Convert Response to an JSON value for interactive editor frontends.
jsonifyResponse :: Response -> TCM ByteString
jsonifyResponse = pure . encode <=< encodeTCM
