{-# LANGUAGE CPP       #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wunused-imports #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Agda.Interaction.Options.Base
    ( CommandLineOptions(..)
    , PragmaOptions(..)
    , OptionError
    , OptionWarning(..), optionWarningName
    , Flag, OptM, runOptM, OptDescr(..), ArgDescr(..)
    , Verbosity, VerboseKey, VerboseLevel
    , ConfluenceCheck(..)
    , DiagnosticsColours(..)
    , EmacsModeCommand(..)
    , PrintAgdaVersion(..)
    , UnicodeOrAscii(..)
    , WarningMode(..)
    , checkOpts
    , parsePragmaOptions
    , parsePluginOptions
    , parseVerboseKey
    , stripRTS
    , defaultOptions
    , defaultInteractionOptions
    , defaultCutOff
    , defaultPragmaOptions
    , optionGroups
    , latexPragmaOptions
    , unsafePragmaOptions
    , recheckBecausePragmaOptionsChanged
    , InfectiveCoinfective(..)
    , InfectiveCoinfectiveOption(..)
    , infectiveCoinfectiveOptions
    , ImpliedPragmaOption(..)
    , impliedPragmaOptions
    , safeFlag
    , mapFlag
    -- Reused by PandocAgda
    , inputFlag
    , standardOptions, deadStandardOptions
    , getOptSimple
    -- * Lenses for 'PragmaOptions'
    , lensOptShowImplicit
    , lensOptShowIrrelevant
    , lensOptUseUnicode
    , lensOptVerbose
    , lensOptProfiling
    , lensOptProp
    , lensOptLevelUniverse
    , lensOptTwoLevel
    , lensOptAllowUnsolved
    , lensOptAllowIncompleteMatch
    , lensOptPositivityCheck
    , lensOptTerminationCheck
    , lensOptTerminationDepth
    , lensOptUniverseCheck, lensOptNoUniverseCheck
    , lensOptOmegaInOmega
    , lensOptCumulativity
    , lensOptSizedTypes
    , lensOptGuardedness
    , lensOptInjectiveTypeConstructors
    , lensOptUniversePolymorphism
    , lensOptIrrelevantProjections
    , lensOptExperimentalIrrelevance
    , lensOptExperimentalLazyInstances
    , lensOptWithoutK
    , lensOptCubicalCompatible
    , lensOptCopatterns
    , lensOptPatternMatching
    , lensOptExactSplit
    , lensOptHiddenArgumentPuns
    , lensOptEta
    , lensOptForcing
    , lensOptProjectionLike
    , lensOptErasure
    , lensOptErasedMatches
    , lensOptEraseRecordParameters
    , lensOptRewriting
    , lensOptLocalRewriting
    , lensOptCubical
    , lensOptGuarded
    , lensOptFirstOrder
    , lensOptRequireUniqueMetaSolutions
    , lensOptPostfixProjections
    , lensOptKeepPatternVariables
    , lensOptInferAbsurdClauses
    , lensOptInstanceSearchDepth
    , lensOptBacktrackingInstances
    , lensOptQualifiedInstances
    , lensOptInversionMaxDepth
    , lensOptSafe
    , lensOptDoubleCheck
    , lensOptSyntacticEquality
    , lensOptWarningMode
    , lensOptCompileMain
    , lensOptCaching
    , lensOptCountClusters
    , lensOptAutoInline
    , lensOptPrintPatternSynonyms
    , lensOptFastReduce
    , lensOptCallByName
    , lensOptConfluenceCheck
    , lensOptCohesion
    , lensOptFlatSplit
    , lensOptPolarity
    , lensOptOccurrence
    , lensOptImportSorts
    , lensOptLoadPrimitives
    , lensOptAllowExec
    , lensOptSaveMetas
    , lensOptShowIdentitySubstitutions
    , lensOptKeepCoveringClauses
    -- * Boolean accessors to 'PragmaOptions' collapsing default
    , optShowImplicit
    , optShowGeneralized
    , optShowIrrelevant
    , optProp
    , optLevelUniverse
    , optTwoLevel
    , optAllowUnsolved
    , optAllowIncompleteMatch
    , optPositivityCheck
    , optTerminationCheck
    , optUniverseCheck
    , optOmegaInOmega
    , optCumulativity
    , optSizedTypes
    , optGuardedness
    , optInjectiveTypeConstructors
    , optUniversePolymorphism
    , optIrrelevantProjections
    , optExperimentalIrrelevance
    , optWithoutK
    , optCubicalCompatible
    , optCopatterns
    , optPatternMatching
    , optHiddenArgumentPuns
    , optEta
    , optForcing
    , optProjectionLike
    , optErasure
    , optErasedMatches
    , optEraseRecordParameters
    , optRewriting
    , optLocalRewriting
    , optGuarded
    , optFirstOrder
    , optRequireUniqueMetaSolutions
    , optPostfixProjections
    , optKeepPatternVariables
    , optInferAbsurdClauses
    , optBacktrackingInstances
    , optQualifiedInstances
    , optSafe
    , optDoubleCheck
    , optCompileNoMain
    , optCaching
    , optCountClusters
    , optAutoInline
    , optPrintPatternSynonyms
    , optFastReduce
    , optCallByName
    , optCohesion
    , optFlatSplit
    , optPolarity
    , optOccurrence
    , optImportSorts
    , optLoadPrimitives
    , optAllowExec
    , optSaveMetas
    , optShowIdentitySubstitutions
    , optKeepCoveringClauses
    , optLargeIndices
    , optForcedArgumentRecursion
    , optQuoteMetas
    -- * Non-boolean accessors to 'PragmaOptions'
    , optConfluenceCheck
    , optCubical
    , optInstanceSearchDepth
    , optInversionMaxDepth
    , optProfiling
    , optSyntacticEquality
    , optTerminationDepth
    , optUseUnicode
    , optVerbose
    , optWarningMode
    ) where

import Prelude hiding ( null, not, (&&), (||) )

import Control.DeepSeq
import Control.Monad        ( (>=>), when, void )
import Control.Monad.Except ( ExceptT, MonadError(throwError), runExceptT )
import Control.Monad.Writer ( Writer, runWriter, MonadWriter(..) )

import Data.Bifunctor           ( second )
import Data.Function            ( (&) )
import Data.List                ( intercalate )
import Data.Maybe
import Data.Set                 ( Set )
import qualified Data.Set as Set

import GHC.Generics (Generic)

import Agda.Utils.GetOpt        ( getOpt', ArgOrder(ReturnInOrder)
                                , OptDescr(..), ArgDescr(..)
                                )
import qualified System.IO.Unsafe as UNSAFE (unsafePerformIO)

import Text.EditDistance
import Text.Read                ( readMaybe )

import Agda.Termination.CutOff  ( CutOff(..), defaultCutOff )

import Agda.Interaction.Library ( OptionsPragma(..), parseLibName )
import Agda.Interaction.Options.Arguments
import Agda.Interaction.Options.Default
import Agda.Interaction.Options.Help
  ( Help(HelpFor, GeneralHelp)
  , string2HelpTopic
  , allHelpTopics
  )
import Agda.Interaction.Options.Types
import Agda.Interaction.Options.Warnings

import Agda.Syntax.Concrete.Glyph ( unsafeSetUnicodeOrAscii, UnicodeOrAscii(..) )
import Agda.Syntax.Common (Cubical(..))
import Agda.Syntax.Common.Pretty
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)

import qualified Agda.Setup.EmacsMode as EmacsMode

import Agda.Utils.Boolean
import Agda.Utils.Function      ( applyWhen, applyUnless )
import Agda.Utils.Functor       ( (<&>) )
import Agda.Utils.Lens          ( Lens', (^.), over, set )
import Agda.Utils.List          ( headWithDefault, initLast1 )
import Agda.Utils.List1         ( List1, pattern (:|), toList )
import qualified Agda.Utils.List1        as List1
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad         ( tell1 )
import Agda.Utils.Null
import Agda.Interaction.Options.ProfileOptions
import Agda.Utils.String        ( unwords1 )
import qualified Agda.Utils.String       as String
import qualified Agda.Utils.Trie as Trie
import Agda.Utils.TypeLits
import Agda.Utils.WithDefault

import Agda.Utils.Impossible

parseVerboseKey :: VerboseKey -> [VerboseKeyItem]
parseVerboseKey = List1.wordsBy (`elem` ['.', ':'])

data ImpliedPragmaOption where
  ImpliesPragmaOption
    :: String -> Bool -> (PragmaOptions -> WithDefault a)
    -> String -> Bool -> (PragmaOptions -> WithDefault b)
    -> ImpliedPragmaOption
    -- ^ The first option having the given value implies the second option having its given value.
    --   For instance, `ImpliesPragmaOption "lossy-unification" True _optFirstOrder
    --                                      "require-unique-meta-solutions" False _optRequireUniqueMetaSolutions`
    --   encodes the fact that --lossy-unification implies --no-require-unique-meta-solutions.

impliedPragmaOptions :: [ImpliedPragmaOption]
impliedPragmaOptions =
  [ ("erase-record-parameters", _optEraseRecordParameters) ==> ("erasure",                          _optErasure)
  , ("erased-matches",          _optErasedMatches)         ==> ("erasure",                          _optErasure)
  , ("flat-split",              _optFlatSplit)             ==> ("cohesion",                         _optCohesion)
  , ("no-load-primitives",      _optLoadPrimitives)        ==> ("no-import-sorts",                  _optImportSorts)
  , ("lossy-unification",       _optFirstOrder)            ==> ("no-require-unique-meta-solutions", _optRequireUniqueMetaSolutions)
  ]
  where
    yesOrNo ('n':'o':'-':s) = (False, s)
    yesOrNo s               = (True, s)
    (nameA, optA) ==> (nameB, optB) = ImpliesPragmaOption stemA valA optA stemB valB optB
      where
        (valA, stemA) = yesOrNo nameA
        (valB, stemB) = yesOrNo nameB

-- collapse defaults
optShowImplicit              :: PragmaOptions -> Bool
optShowGeneralized           :: PragmaOptions -> Bool
optShowIrrelevant            :: PragmaOptions -> Bool
optProp                      :: PragmaOptions -> Bool
optLevelUniverse             :: PragmaOptions -> Bool
optTwoLevel                  :: PragmaOptions -> Bool
optAllowUnsolved             :: PragmaOptions -> Bool
optAllowIncompleteMatch      :: PragmaOptions -> Bool
optPositivityCheck           :: PragmaOptions -> Bool
optTerminationCheck          :: PragmaOptions -> Bool
optUniverseCheck             :: PragmaOptions -> Bool
optOmegaInOmega              :: PragmaOptions -> Bool
optCumulativity              :: PragmaOptions -> Bool
optSizedTypes                :: PragmaOptions -> Bool
optGuardedness               :: PragmaOptions -> Bool
optInjectiveTypeConstructors :: PragmaOptions -> Bool
optUniversePolymorphism      :: PragmaOptions -> Bool
optIrrelevantProjections     :: PragmaOptions -> Bool
optExperimentalIrrelevance   :: PragmaOptions -> Bool
optWithoutK                  :: PragmaOptions -> Bool
optCubicalCompatible         :: PragmaOptions -> Bool
optCopatterns                :: PragmaOptions -> Bool
optPatternMatching           :: PragmaOptions -> Bool
optHiddenArgumentPuns        :: PragmaOptions -> Bool
optEta                       :: PragmaOptions -> Bool
optForcing                   :: PragmaOptions -> Bool
optProjectionLike            :: PragmaOptions -> Bool
-- | 'optErasure' is implied by 'optEraseRecordParameters'.
--   'optErasure' is also implied by an explicitly given `--erased-matches`.
optErasure                   :: PragmaOptions -> Bool
optErasedMatches             :: PragmaOptions -> Bool
optEraseRecordParameters     :: PragmaOptions -> Bool
optRewriting                 :: PragmaOptions -> Bool
optLocalRewriting            :: PragmaOptions -> Bool
optGuarded                   :: PragmaOptions -> Bool
optFirstOrder                :: PragmaOptions -> Bool
optRequireUniqueMetaSolutions :: PragmaOptions -> Bool
optPostfixProjections        :: PragmaOptions -> Bool
optKeepPatternVariables      :: PragmaOptions -> Bool
optInferAbsurdClauses        :: PragmaOptions -> Bool
optBacktrackingInstances     :: PragmaOptions -> Bool
optQualifiedInstances        :: PragmaOptions -> Bool
optSafe                      :: PragmaOptions -> Bool
optDoubleCheck               :: PragmaOptions -> Bool
optCompileNoMain             :: PragmaOptions -> Bool
optCaching                   :: PragmaOptions -> Bool
optCountClusters             :: PragmaOptions -> Bool
optAutoInline                :: PragmaOptions -> Bool
optPrintPatternSynonyms      :: PragmaOptions -> Bool
optFastReduce                :: PragmaOptions -> Bool
optCallByName                :: PragmaOptions -> Bool
-- | 'optCohesion' is implied by 'optFlatSplit'.
optCohesion                  :: PragmaOptions -> Bool
optFlatSplit                 :: PragmaOptions -> Bool
optPolarity                  :: PragmaOptions -> Bool
optOccurrence                :: PragmaOptions -> Bool
-- | 'optImportSorts' requires 'optLoadPrimitives'.
optImportSorts               :: PragmaOptions -> Bool
optLoadPrimitives            :: PragmaOptions -> Bool
optAllowExec                 :: PragmaOptions -> Bool
optSaveMetas                 :: PragmaOptions -> Bool
optShowIdentitySubstitutions :: PragmaOptions -> Bool
optKeepCoveringClauses       :: PragmaOptions -> Bool
optLargeIndices              :: PragmaOptions -> Bool
optForcedArgumentRecursion   :: PragmaOptions -> Bool

optShowImplicit              = collapseDefault . _optShowImplicit
optShowGeneralized           = collapseDefault . _optShowGeneralized
optShowIrrelevant            = collapseDefault . _optShowIrrelevant
optProp                      = collapseDefault . _optProp
optLevelUniverse             = collapseDefault . _optLevelUniverse
optTwoLevel                  = collapseDefault . _optTwoLevel
optAllowUnsolved             = collapseDefault . _optAllowUnsolved
optAllowIncompleteMatch      = collapseDefault . _optAllowIncompleteMatch
optPositivityCheck           = collapseDefault . _optPositivityCheck
optTerminationCheck          = collapseDefault . _optTerminationCheck
optUniverseCheck             = collapseDefault . _optUniverseCheck
optOmegaInOmega              = collapseDefault . _optOmegaInOmega
optCumulativity              = collapseDefault . _optCumulativity
optSizedTypes                = collapseDefault . _optSizedTypes
optGuardedness               = collapseDefault . _optGuardedness
optInjectiveTypeConstructors = collapseDefault . _optInjectiveTypeConstructors
optUniversePolymorphism      = collapseDefault . _optUniversePolymorphism
optIrrelevantProjections     = collapseDefault . _optIrrelevantProjections
optExperimentalIrrelevance   = collapseDefault . _optExperimentalIrrelevance
optWithoutK                  = collapseDefault . _optWithoutK
optCubicalCompatible         = collapseDefault . _optCubicalCompatible
optCopatterns                = collapseDefault . _optCopatterns
optPatternMatching           = collapseDefault . _optPatternMatching
optHiddenArgumentPuns        = collapseDefault . _optHiddenArgumentPuns
optEta                       = collapseDefault . _optEta
optForcing                   = collapseDefault . _optForcing
optProjectionLike            = collapseDefault . _optProjectionLike
-- --erase-record-parameters implies --erasure
optErasure                   = collapseDefault . _optErasure || optEraseRecordParameters || (Value True ==) . _optErasedMatches
optErasedMatches             = collapseDefault . _optErasedMatches && optErasure
optEraseRecordParameters     = collapseDefault . _optEraseRecordParameters
optRewriting                 = collapseDefault . _optRewriting
optLocalRewriting            = collapseDefault . _optLocalRewriting
optGuarded                   = collapseDefault . _optGuarded
optFirstOrder                = collapseDefault . _optFirstOrder
optRequireUniqueMetaSolutions = collapseDefault . _optRequireUniqueMetaSolutions && not . optFirstOrder
-- --lossy-unification implies --no-require-unique-meta-solutions
optPostfixProjections        = collapseDefault . _optPostfixProjections
optKeepPatternVariables      = collapseDefault . _optKeepPatternVariables
optInferAbsurdClauses        = collapseDefault . _optInferAbsurdClauses
optBacktrackingInstances     = collapseDefault . _optBacktrackingInstances
optQualifiedInstances        = collapseDefault . _optQualifiedInstances
optSafe                      = collapseDefault . _optSafe
optDoubleCheck               = collapseDefault . _optDoubleCheck
optCompileNoMain             = not . collapseDefault . _optCompileMain
optCaching                   = collapseDefault . _optCaching
optCountClusters             = collapseDefault . _optCountClusters
optAutoInline                = collapseDefault . _optAutoInline
optPrintPatternSynonyms      = collapseDefault . _optPrintPatternSynonyms
optFastReduce                = collapseDefault . _optFastReduce
optCallByName                = collapseDefault . _optCallByName
-- --flat-split implies --cohesion
optCohesion                  = collapseDefault . _optCohesion      || optFlatSplit
optFlatSplit                 = collapseDefault . _optFlatSplit
optPolarity                  = collapseDefault . _optPolarity
optOccurrence                = collapseDefault . _optOccurrence
-- --no-load-primitives implies --no-import-sorts
optImportSorts               = collapseDefault . _optImportSorts   && optLoadPrimitives
optLoadPrimitives            = collapseDefault . _optLoadPrimitives
optAllowExec                 = collapseDefault . _optAllowExec
optSaveMetas                 = collapseDefault . _optSaveMetas
optShowIdentitySubstitutions = collapseDefault . _optShowIdentitySubstitutions
optKeepCoveringClauses       = collapseDefault . _optKeepCoveringClauses
optLargeIndices              = collapseDefault . _optLargeIndices
optForcedArgumentRecursion   = collapseDefault . _optForcedArgumentRecursion
optQuoteMetas                = collapseDefault . _optQuoteMetas

-- Collapse defaults (non-Bool)

optUseUnicode                :: PragmaOptions -> UnicodeOrAscii
optUseUnicode                = collapseDefault . _optUseUnicode

-- Extra trivial accessors (keep in alphabetical order)

optConfluenceCheck     :: PragmaOptions -> _
optCubical             :: PragmaOptions -> _
optInstanceSearchDepth :: PragmaOptions -> _
optInversionMaxDepth   :: PragmaOptions -> _
optProfiling           :: PragmaOptions -> _
optSyntacticEquality   :: PragmaOptions -> _
optTerminationDepth    :: PragmaOptions -> _
optVerbose             :: PragmaOptions -> _
optWarningMode         :: PragmaOptions -> _

optConfluenceCheck     = _optConfluenceCheck
optCubical             = _optCubical
optInstanceSearchDepth = _optInstanceSearchDepth
optInversionMaxDepth   = _optInversionMaxDepth
optProfiling           = _optProfiling
optSyntacticEquality   = _optSyntacticEquality
optTerminationDepth    = _optTerminationDepth
optVerbose             = _optVerbose
optWarningMode         = _optWarningMode

-- Lenses for PragmaOptions
-- N.B.: We use PartialTypeSignatures here to not repeat default values (DRY!).

lensOptShowImplicit :: Lens' PragmaOptions _
lensOptShowImplicit f o = f (_optShowImplicit o) <&> \ i -> o{ _optShowImplicit = i }

lensOptShowIrrelevant :: Lens' PragmaOptions _
lensOptShowIrrelevant f o = f (_optShowIrrelevant o) <&> \ i -> o{ _optShowIrrelevant = i }

lensOptUseUnicode :: Lens' PragmaOptions _
lensOptUseUnicode f o = f (_optUseUnicode o) <&> \ i -> o{ _optUseUnicode = i }

lensOptVerbose :: Lens' PragmaOptions _
lensOptVerbose f o = f (_optVerbose o) <&> \ i -> o{ _optVerbose = i }

lensOptProfiling :: Lens' PragmaOptions _
lensOptProfiling f o = f (_optProfiling o) <&> \ i -> o{ _optProfiling = i }

lensOptProp :: Lens' PragmaOptions _
lensOptProp f o = f (_optProp o) <&> \ i -> o{ _optProp = i }

lensOptLevelUniverse :: Lens' PragmaOptions _
lensOptLevelUniverse f o = f (_optLevelUniverse o) <&> \ i -> o{ _optLevelUniverse = i }

lensOptTwoLevel :: Lens' PragmaOptions _
lensOptTwoLevel f o = f (_optTwoLevel o) <&> \ i -> o{ _optTwoLevel = i }

lensOptAllowUnsolved :: Lens' PragmaOptions _
lensOptAllowUnsolved f o = f (_optAllowUnsolved o) <&> \ i -> o{ _optAllowUnsolved = i }

lensOptAllowIncompleteMatch :: Lens' PragmaOptions _
lensOptAllowIncompleteMatch f o = f (_optAllowIncompleteMatch o) <&> \ i -> o{ _optAllowIncompleteMatch = i }

lensOptPositivityCheck :: Lens' PragmaOptions _
lensOptPositivityCheck f o = f (_optPositivityCheck o) <&> \ i -> o{ _optPositivityCheck = i }

lensOptTerminationCheck :: Lens' PragmaOptions _
lensOptTerminationCheck f o = f (_optTerminationCheck o) <&> \ i -> o{ _optTerminationCheck = i }

lensOptTerminationDepth :: Lens' PragmaOptions _
lensOptTerminationDepth f o = f (_optTerminationDepth o) <&> \ i -> o{ _optTerminationDepth = i }

lensOptUniverseCheck :: Lens' PragmaOptions _
lensOptUniverseCheck f o = f (_optUniverseCheck o) <&> \ i -> o{ _optUniverseCheck = i }

lensOptNoUniverseCheck :: Lens' PragmaOptions _
lensOptNoUniverseCheck f o = f (not' $ _optUniverseCheck o) <&> \ i -> o{ _optUniverseCheck = not' i }

lensOptOmegaInOmega :: Lens' PragmaOptions _
lensOptOmegaInOmega f o = f (_optOmegaInOmega o) <&> \ i -> o{ _optOmegaInOmega = i }

lensOptCumulativity :: Lens' PragmaOptions _
lensOptCumulativity f o = f (_optCumulativity o) <&> \ i -> o{ _optCumulativity = i }

lensOptSizedTypes :: Lens' PragmaOptions _
lensOptSizedTypes f o = f (_optSizedTypes o) <&> \ i -> o{ _optSizedTypes = i }

lensOptGuardedness :: Lens' PragmaOptions _
lensOptGuardedness f o = f (_optGuardedness o) <&> \ i -> o{ _optGuardedness = i }

lensOptInjectiveTypeConstructors :: Lens' PragmaOptions _
lensOptInjectiveTypeConstructors f o = f (_optInjectiveTypeConstructors o) <&> \ i -> o{ _optInjectiveTypeConstructors = i }

lensOptUniversePolymorphism :: Lens' PragmaOptions _
lensOptUniversePolymorphism f o = f (_optUniversePolymorphism o) <&> \ i -> o{ _optUniversePolymorphism = i }

lensOptIrrelevantProjections :: Lens' PragmaOptions _
lensOptIrrelevantProjections f o = f (_optIrrelevantProjections o) <&> \ i -> o{ _optIrrelevantProjections = i }

lensOptExperimentalIrrelevance :: Lens' PragmaOptions _
lensOptExperimentalIrrelevance f o = f (_optExperimentalIrrelevance o) <&> \ i -> o{ _optExperimentalIrrelevance = i }

lensOptWithoutK :: Lens' PragmaOptions _
lensOptWithoutK f o = f (_optWithoutK o) <&> \ i -> o{ _optWithoutK = i }

lensOptCubicalCompatible :: Lens' PragmaOptions _
lensOptCubicalCompatible f o = f (_optCubicalCompatible o) <&> \ i -> o{ _optCubicalCompatible = i }

lensOptCopatterns :: Lens' PragmaOptions _
lensOptCopatterns f o = f (_optCopatterns o) <&> \ i -> o{ _optCopatterns = i }

lensOptPatternMatching :: Lens' PragmaOptions _
lensOptPatternMatching f o = f (_optPatternMatching o) <&> \ i -> o{ _optPatternMatching = i }

lensOptExactSplit :: Lens' PragmaOptions _
lensOptExactSplit f o = f (_optExactSplit o) <&> \ i -> o{ _optExactSplit = i }

lensOptHiddenArgumentPuns :: Lens' PragmaOptions _
lensOptHiddenArgumentPuns f o = f (_optHiddenArgumentPuns o) <&> \ i -> o{ _optHiddenArgumentPuns = i }

lensOptEta :: Lens' PragmaOptions _
lensOptEta f o = f (_optEta o) <&> \ i -> o{ _optEta = i }

lensOptForcing :: Lens' PragmaOptions _
lensOptForcing f o = f (_optForcing o) <&> \ i -> o{ _optForcing = i }

lensOptProjectionLike :: Lens' PragmaOptions _
lensOptProjectionLike f o = f (_optProjectionLike o) <&> \ i -> o{ _optProjectionLike = i }

lensOptErasure :: Lens' PragmaOptions _
lensOptErasure f o = f (_optErasure o) <&> \ i -> o{ _optErasure = i }

lensOptErasedMatches :: Lens' PragmaOptions _
lensOptErasedMatches f o = f (_optErasedMatches o) <&> \ i -> o{ _optErasedMatches = i }

lensOptEraseRecordParameters :: Lens' PragmaOptions _
lensOptEraseRecordParameters f o = f (_optEraseRecordParameters o) <&> \ i -> o{ _optEraseRecordParameters = i }

lensOptRewriting :: Lens' PragmaOptions _
lensOptRewriting f o = f (_optRewriting o) <&> \ i -> o{ _optRewriting = i }

lensOptLocalRewriting :: Lens' PragmaOptions _
lensOptLocalRewriting f o = f (_optLocalRewriting o) <&> \ i -> o{ _optLocalRewriting = i }

lensOptCubical :: Lens' PragmaOptions _
lensOptCubical f o = f (_optCubical o) <&> \ i -> o{ _optCubical = i }

lensOptGuarded :: Lens' PragmaOptions _
lensOptGuarded f o = f (_optGuarded o) <&> \ i -> o{ _optGuarded = i }

lensOptFirstOrder :: Lens' PragmaOptions _
lensOptFirstOrder f o = f (_optFirstOrder o) <&> \ i -> o{ _optFirstOrder = i }

lensOptRequireUniqueMetaSolutions :: Lens' PragmaOptions _
lensOptRequireUniqueMetaSolutions f o = f (_optRequireUniqueMetaSolutions o) <&> \ i -> o{ _optRequireUniqueMetaSolutions = i }

lensOptPostfixProjections :: Lens' PragmaOptions _
lensOptPostfixProjections f o = f (_optPostfixProjections o) <&> \ i -> o{ _optPostfixProjections = i }

lensOptKeepPatternVariables :: Lens' PragmaOptions _
lensOptKeepPatternVariables f o = f (_optKeepPatternVariables o) <&> \ i -> o{ _optKeepPatternVariables = i }

lensOptInferAbsurdClauses :: Lens' PragmaOptions _
lensOptInferAbsurdClauses f o = f (_optInferAbsurdClauses o) <&> \ i -> o{ _optInferAbsurdClauses = i }

lensOptInstanceSearchDepth :: Lens' PragmaOptions _
lensOptInstanceSearchDepth f o = f (_optInstanceSearchDepth o) <&> \ i -> o{ _optInstanceSearchDepth = i }

lensOptBacktrackingInstances :: Lens' PragmaOptions _
lensOptBacktrackingInstances f o = f (_optBacktrackingInstances o) <&> \ i -> o{ _optBacktrackingInstances = i }

lensOptQualifiedInstances :: Lens' PragmaOptions _
lensOptQualifiedInstances f o = f (_optQualifiedInstances o) <&> \ i -> o{ _optQualifiedInstances = i }

lensOptInversionMaxDepth :: Lens' PragmaOptions _
lensOptInversionMaxDepth f o = f (_optInversionMaxDepth o) <&> \ i -> o{ _optInversionMaxDepth = i }

lensOptSafe :: Lens' PragmaOptions _
lensOptSafe f o = f (_optSafe o) <&> \ i -> o{ _optSafe = i }

lensOptDoubleCheck :: Lens' PragmaOptions _
lensOptDoubleCheck f o = f (_optDoubleCheck o) <&> \ i -> o{ _optDoubleCheck = i }

lensOptSyntacticEquality :: Lens' PragmaOptions _
lensOptSyntacticEquality f o = f (_optSyntacticEquality o) <&> \ i -> o{ _optSyntacticEquality = i }

lensOptWarningMode :: Lens' PragmaOptions _
lensOptWarningMode f o = f (_optWarningMode o) <&> \ i -> o{ _optWarningMode = i }

lensOptCompileMain :: Lens' PragmaOptions _
lensOptCompileMain f o = f (_optCompileMain o) <&> \ i -> o{ _optCompileMain = i }

lensOptCaching :: Lens' PragmaOptions _
lensOptCaching f o = f (_optCaching o) <&> \ i -> o{ _optCaching = i }

lensOptCountClusters :: Lens' PragmaOptions _
lensOptCountClusters f o = f (_optCountClusters o) <&> \ i -> o{ _optCountClusters = i }

lensOptAutoInline :: Lens' PragmaOptions _
lensOptAutoInline f o = f (_optAutoInline o) <&> \ i -> o{ _optAutoInline = i }

lensOptPrintPatternSynonyms :: Lens' PragmaOptions _
lensOptPrintPatternSynonyms f o = f (_optPrintPatternSynonyms o) <&> \ i -> o{ _optPrintPatternSynonyms = i }

lensOptFastReduce :: Lens' PragmaOptions _
lensOptFastReduce f o = f (_optFastReduce o) <&> \ i -> o{ _optFastReduce = i }

lensOptCallByName :: Lens' PragmaOptions _
lensOptCallByName f o = f (_optCallByName o) <&> \ i -> o{ _optCallByName = i }

lensOptConfluenceCheck :: Lens' PragmaOptions _
lensOptConfluenceCheck f o = f (_optConfluenceCheck o) <&> \ i -> o{ _optConfluenceCheck = i }

lensOptCohesion :: Lens' PragmaOptions _
lensOptCohesion f o = f (_optCohesion o) <&> \ i -> o{ _optCohesion = i }

lensOptFlatSplit :: Lens' PragmaOptions _
lensOptFlatSplit f o = f (_optFlatSplit o) <&> \ i -> o{ _optFlatSplit = i }

lensOptPolarity :: Lens' PragmaOptions _
lensOptPolarity f o = f (_optPolarity o) <&> \ i -> o{ _optPolarity = i}

lensOptOccurrence :: Lens' PragmaOptions _
lensOptOccurrence f o =
  f (_optOccurrence o) <&> \ i -> o{ _optOccurrence = i}

lensOptImportSorts :: Lens' PragmaOptions _
lensOptImportSorts f o = f (_optImportSorts o) <&> \ i -> o{ _optImportSorts = i }

lensOptLoadPrimitives :: Lens' PragmaOptions _
lensOptLoadPrimitives f o = f (_optLoadPrimitives o) <&> \ i -> o{ _optLoadPrimitives = i }

lensOptAllowExec :: Lens' PragmaOptions _
lensOptAllowExec f o = f (_optAllowExec o) <&> \ i -> o{ _optAllowExec = i }

lensOptSaveMetas :: Lens' PragmaOptions _
lensOptSaveMetas f o = f (_optSaveMetas o) <&> \ i -> o{ _optSaveMetas = i }

lensOptShowIdentitySubstitutions :: Lens' PragmaOptions _
lensOptShowIdentitySubstitutions f o = f (_optShowIdentitySubstitutions o) <&> \ i -> o{ _optShowIdentitySubstitutions = i }

lensOptKeepCoveringClauses :: Lens' PragmaOptions _
lensOptKeepCoveringClauses f o = f (_optKeepCoveringClauses o) <&> \ i -> o{ _optKeepCoveringClauses = i }

lensOptLargeIndices :: Lens' PragmaOptions _
lensOptLargeIndices f o = f (_optLargeIndices o) <&> \ i -> o{ _optLargeIndices = i }

lensOptForcedArgumentRecursion :: Lens' PragmaOptions _
lensOptForcedArgumentRecursion f o = f (_optForcedArgumentRecursion o) <&> \ i -> o{ _optForcedArgumentRecursion = i }

lensOptExperimentalLazyInstances :: Lens' PragmaOptions _
lensOptExperimentalLazyInstances f o = f (_optExperimentalLazyInstances o) <&> \ i -> o{ _optExperimentalLazyInstances = i }

lensOptQuoteMetas :: Lens' PragmaOptions _
lensOptQuoteMetas f o = f (_optQuoteMetas o) <&> \ i -> o{ _optQuoteMetas = i }

-- | Map a function over the long options. Also removes the short options.
--   Will be used to add the plugin name to the plugin options.
mapFlag :: (String -> String) -> OptDescr a -> OptDescr a
mapFlag f (Option _ long arg descr) = Option [] (map f long) arg descr

defaultInteractionOptions :: PragmaOptions
defaultInteractionOptions = defaultPragmaOptions

-- | The options parse monad 'OptM' collects warnings that are not discarded
--   when a fatal error occurrs
newtype OptM a = OptM { unOptM :: ExceptT OptionError (Writer OptionWarnings) a }
  deriving (Functor, Applicative, Monad, MonadError OptionError, MonadWriter OptionWarnings)

type OptionError = String
type OptionWarnings = [OptionWarning]

runOptM :: OptM opts -> (Either OptionError opts, OptionWarnings)
runOptM = runWriter . runExceptT . unOptM

{- | @f :: Flag opts@  is an action on the option record that results from
     parsing an option.  @f opts@ produces either an error message or an
     updated options record
-}
type Flag opts = opts -> OptM opts

-- | Warnings when parsing options.

data OptionWarning
  = OptionRenamed { oldOptionName :: String, newOptionName :: String }
      -- ^ Name of option changed in a newer version of Agda.
  | WarningProblem WarningModeError
      -- ^ A problem with setting or unsetting a warning.
  | LocalRewritingConfluenceCheck
      -- ^ Confluence checking for local rewrite rules is unimplemented.
  deriving (Show, Generic)

instance NFData OptionWarning

instance Pretty OptionWarning where
  pretty = \case
    OptionRenamed old new -> hsep
      [ "Option", option old, "is deprecated, please use", option new, "instead" ]
    WarningProblem err -> pretty (prettyWarningModeError err) <+> "See --help=warning."
    LocalRewritingConfluenceCheck -> fsep $ pwords "Confluence checking (--confluence-check or --local-confluence-check) is not yet implemented for local rewrite rules (--local-rewriting)"
    where
    option = text . ("--" ++)

optionWarningName :: OptionWarning -> WarningName
optionWarningName = \case
  OptionRenamed{} -> OptionRenamed_
  WarningProblem{} -> WarningProblem_
  LocalRewritingConfluenceCheck -> LocalRewritingConfluenceCheck_

-- | Checks that the given options are consistent.
--   Also makes adjustments (e.g. when one option implies another).

checkOpts :: (MonadError OptionError m, MonadWriter OptionWarnings m)
  => CommandLineOptions -> m CommandLineOptions
checkOpts opts = do
  -- NOTE: This is a temporary hold-out until --vim can be converted into a backend or plugin,
  -- whose options compatibility currently is checked in `Agda.Compiler.Backend`.
  --
  -- Additionally, note that some options checking is performed in `Agda.Main`
  -- in which the top-level frontend and backend interactors are selected.
  --
  -- Those checks are not represented here, because:
  --   - They are used solely for selecting the initial executon mode; they
  --     don't need to be checked on a per-module etc basis.
  --   - I hope/expect that the presence of those specific flags will be eventually
  --     abstracted out (like the Backends' internal flags), so that they are invisible
  --     to the rest of the type-checking system.
  when (optGenerateVimFile opts && optOnlyScopeChecking opts) $
    throwError $ "The --only-scope-checking flag cannot be combined with --vim."

  lensPragmaOptions checkPragmaOptions opts

-- | Check for pragma option consistency and make adjustments.

checkPragmaOptions :: (MonadError OptionError m, MonadWriter OptionWarnings m)
  => PragmaOptions -> m PragmaOptions
checkPragmaOptions opts = do

  -- Check for errors in pragma options.

  when ((optEraseRecordParameters `butNot` optErasure) opts) $
    throwError
      "The option --erase-record-parameters requires the use of --erasure"

  when (isJust (optConfluenceCheck opts) && optLocalRewriting opts) $
    tell1 LocalRewritingConfluenceCheck

#ifndef COUNT_CLUSTERS
  when (optCountClusters opts) $
    throwError
      "Cluster counting has not been enabled in this build of Agda."
#endif

  -- Perform corrections in pragma options.

  return $ opts

    -- -WTerminationIssue iff --termination-check
    & conformWarningToOption TerminationIssue_ optTerminationCheck

    -- -WNotStrictlyPositive iff --positivity-check
    . conformWarningToOption NotStrictlyPositive_ optPositivityCheck

    -- unsolvedWarnings iff --no-allow-unsolved-metas
    . conformWarningsToOption unsolvedWarnings (not . optAllowUnsolved)

    -- incompleteMatchWarnings iff --no-allow-incomplete-matches
    . conformWarningsToOption incompleteMatchWarnings (not . optAllowIncompleteMatch)

-- | Activate warning when and only when option is on.
conformWarningToOption ::
     WarningName
       -- ^ Warning to toggle.
  -> (PragmaOptions -> Bool)
       -- ^ Which flag to conform to?
  -> PragmaOptions
       -- ^ Options to modify.
  -> PragmaOptions
       -- ^ Modified options.
conformWarningToOption = conformWarningsToOption . Set.singleton

-- | Activate warnings when option is on and deactivate them when option is off.
conformWarningsToOption ::
     Set WarningName
       -- ^ Warnings to toggle.
  -> (PragmaOptions -> Bool)
       -- ^ Which flag to conform to?
  -> PragmaOptions
       -- ^ Options to modify.
  -> PragmaOptions
       -- ^ Modified options.
conformWarningsToOption ws f opts =
  over (lensOptWarningMode . warningSet) (if f opts then (`Set.union` ws) else (Set.\\ ws)) opts

-- | Check for unsafe pragmas. Gives a list of used unsafe flags.

unsafePragmaOptions :: PragmaOptions -> [String]
unsafePragmaOptions opts =
  [ "--allow-unsolved-metas"            | optAllowUnsolved opts                             ] ++
  [ "--allow-incomplete-matches"        | optAllowIncompleteMatch opts                      ] ++
  [ "--no-positivity-check"             | not (optPositivityCheck opts)                     ] ++
  [ "--no-termination-check"            | not (optTerminationCheck opts)                    ] ++
  [ "--type-in-type"                    | not (optUniverseCheck opts)                       ] ++
  [ "--omega-in-omega"                  | optOmegaInOmega opts                              ] ++
  [ "--sized-types"                     | optSizedTypes opts                                ] ++
  [ "--injective-type-constructors"     | optInjectiveTypeConstructors opts                 ] ++
  [ "--irrelevant-projections"          | optIrrelevantProjections opts                     ] ++
  [ "--experimental-irrelevance"        | optExperimentalIrrelevance opts                   ] ++
  [ "--rewriting"                       | optRewriting opts                                 ] ++
  [ "--local-rewriting"                 | optLocalRewriting opts                            ]
  ++
  [ "--cubical=compatible and --with-K" | optCubicalCompatible opts, not (optWithoutK opts) ] ++
  [ "--without-K and --flat-split"      | optWithoutK opts, optFlatSplit opts               ] ++
  [ "--cumulativity"                    | optCumulativity opts                              ] ++
  [ "--allow-exec"                      | optAllowExec opts                                 ] ++
  [ "--no-load-primitives"              | not $ optLoadPrimitives opts                      ] ++
  [ "--without-K and --large-indices"   | optWithoutK opts, optLargeIndices opts            ] ++
  [ "--large-indices and --forced-argument-recursion"
  | optLargeIndices opts, optForcedArgumentRecursion opts ] ++
  []

-- | This function returns 'True' if the file should be rechecked.

recheckBecausePragmaOptionsChanged
  :: PragmaOptions
     -- ^ The options that were used to check the file.
  -> PragmaOptions
     -- ^ The options that are currently in effect.
  -> Bool
recheckBecausePragmaOptionsChanged used current =
  blankOut used /= blankOut current
  where
  -- "Blank out" irrelevant options.
  -- It does not matter what we replace them with, so we take the null value.
  blankOut opts = opts
    { _optShowImplicit              = empty
    , _optShowIrrelevant            = empty
    , _optVerbose                   = empty
    , _optProfiling                 = empty
    , _optPostfixProjections        = empty
    , _optCompileMain               = empty
    , _optCaching                   = empty
    , _optCountClusters             = empty
    , _optPrintPatternSynonyms      = empty
    , _optShowIdentitySubstitutions = empty
    , _optKeepPatternVariables      = empty
    }

-- | Descriptions of infective and coinfective options.

data InfectiveCoinfectiveOption = ICOption
  { icOptionActive :: PragmaOptions -> Bool
    -- ^ Is the option active?
  , icOptionDescription :: String
    -- ^ A description of the option (typically a flag that activates
    -- the option).
  , icOptionKind :: InfectiveCoinfective
    -- ^ Is the option (roughly speaking) infective or coinfective?
  , icOptionOK :: PragmaOptions -> PragmaOptions -> Bool
    -- ^ This function returns 'True' exactly when, from the
    -- perspective of the option in question, the options in the
    -- current module (the first argument) are compatible with the
    -- options in a given imported module (the second argument).
  , icOptionWarning :: TopLevelModuleName -> Doc
    -- ^ A warning message that should be used if this option is not
    -- used correctly. The given module name is the name of an
    -- imported module for which 'icOptionOK' failed.
  }

-- | A standard infective option: If the option is active in an
-- imported module, then it must be active in the current module.

infectiveOption
  :: (PragmaOptions -> Bool)
     -- ^ Is the option active?
  -> String
    -- ^ A description of the option.
  -> InfectiveCoinfectiveOption
infectiveOption opt s = ICOption
  { icOptionActive      = opt
  , icOptionDescription = s
  , icOptionKind        = Infective
  , icOptionOK          = \current imported ->
                           opt imported <= opt current
  , icOptionWarning     = \m -> fsep $
      pwords "Importing module" ++ [pretty m] ++ pwords "using the" ++
      [text s] ++ pwords "flag from a module which does not."
  }

-- | A standard coinfective option: If the option is active in the
-- current module, then it must be active in all imported modules.

coinfectiveOption
  :: (PragmaOptions -> Bool)
     -- ^ Is the option active?
  -> String
    -- ^ A description of the option.
  -> InfectiveCoinfectiveOption
coinfectiveOption opt s = ICOption
  { icOptionActive      = opt
  , icOptionDescription = s
  , icOptionKind        = Coinfective
  , icOptionOK          = \current imported ->
                           opt current <= opt imported
  , icOptionWarning     = \m -> fsep $
      pwords "Importing module" ++ [pretty m] ++
      pwords "not using the" ++ [text s] ++
      pwords "flag from a module which does."
  }

-- | Infective and coinfective options.
--
-- Note that @--cubical[=full]@ and @--cubical=erased@ are \"jointly
-- infective\": if one of them is used in one module, then one or the
-- other must be used in all modules that depend on this module.

infectiveCoinfectiveOptions :: [InfectiveCoinfectiveOption]
infectiveCoinfectiveOptions =
  [ coinfectiveOption optSafe                 "--safe"
  , coinfectiveOption optWithoutK             "--without-K"
  , cubicalCompatible
  , coinfectiveOption (not . optUniversePolymorphism)
                                              "--no-universe-polymorphism"
  , coinfectiveOption (not . optCumulativity) "--no-cumulativity"
  , coinfectiveOption optLevelUniverse        "--level-universe"
  , infectiveOption (isJust . optCubical)     "--cubical[={full,erased,no-glue}]"
  , cubicalWithoutGlue
  , infectiveOption optGuarded                "--guarded"
  , infectiveOption optProp                   "--prop"
  , infectiveOption optTwoLevel               "--two-level"
  , infectiveOption optRewriting              "--rewriting"
  , infectiveOption optLocalRewriting         "--local-rewriting"
  , infectiveOption optSizedTypes             "--sized-types"
  , infectiveOption optGuardedness            "--guardedness"
  , infectiveOption optFlatSplit              "--flat-split"
  , infectiveOption optPolarity               "--polarity"
  , infectiveOption optCohesion               "--cohesion"
  , infectiveOption optErasure                "--erasure"
  , infectiveOption optErasedMatches          "--erased-matches"
  ]
  where
  cubicalCompatible =
    (coinfectiveOption optCubicalCompatible "--cubical=compatible")
      { icOptionOK = \current imported ->
        -- One must use --cubical=compatible in the imported module if
        -- it is used in the current module, except if the current
        -- module also uses --with-K and not --safe, and the imported
        -- module uses --with-K.
        if optCubicalCompatible current
        then optCubicalCompatible imported
               ||
             not (optWithoutK imported)
               &&
             not (optWithoutK current)
               &&
             not (optSafe current)
        else True
      }

  cubicalWithoutGlue =
    let flagName = "--cubical=no-glue" in
    (infectiveOption (\o -> optCubical o == Just CWithoutGlue) flagName)
      { icOptionOK = \current imported ->
        -- If the current module uses Cubical without glue,
        -- then the imported modules cannot use glue.
          case (optCubical current, optCubical imported) of
            (Just CWithoutGlue, Just CFull)   -> False
            (Just CWithoutGlue, Just CErased) -> False
            _ -> True
      , icOptionWarning = \m -> fsep $
          pwords "Importing module" ++ [pretty m] ++
          pwords "which might contain glue to a module with the option" ++
          pwords (flagName ++ ".")
      }

inputFlag :: FilePath -> Flag CommandLineOptions
inputFlag f o =
    case optInputFile o of
        Nothing  -> return $ o { optInputFile = Just f }
        Just _   -> throwError "only one input file allowed"

printAgdaDataDirFlag :: Flag CommandLineOptions
printAgdaDataDirFlag o = return $ o { optPrintAgdaDataDir = True }

printAgdaAppDirFlag :: Flag CommandLineOptions
printAgdaAppDirFlag o = return $ o { optPrintAgdaAppDir = True }

printOptionsFlag :: Flag CommandLineOptions
printOptionsFlag o = return $ o { optPrintOptions = True }

setupFlag :: Flag CommandLineOptions
setupFlag o = return $ o { optSetup = True }

versionFlag :: Flag CommandLineOptions
versionFlag o = return $ o { optPrintVersion = Just PrintAgdaVersion }

numericVersionFlag :: Flag CommandLineOptions
numericVersionFlag o = return $ o { optPrintVersion = Just PrintAgdaNumericVersion }

helpFlag :: Maybe String -> Flag CommandLineOptions
helpFlag Nothing    o = return $ o { optPrintHelp = Just GeneralHelp }
helpFlag (Just str) o = case string2HelpTopic str of
  Just hpt -> return $ o { optPrintHelp = Just (HelpFor hpt) }
  Nothing -> throwError $ concat
    [ "unknown help topic ", str, " (", printHelpTopics "topic", ")" ]

-- | Helper to explain @--help@.
printHelpTopics :: String -> String
printHelpTopics mvar = concat
  [ "available"
  , ifNull mvar "" {-else-} \ topic -> " " ++ String.pluralS allHelpTopics topic
  , ": "
  , intercalate ", " $ map fst allHelpTopics
  ]

emacsModeFlag :: String -> Flag CommandLineOptions
emacsModeFlag s o
  | s == EmacsMode.setupFlag   = add EmacsModeSetup
  | s == EmacsMode.compileFlag = add EmacsModeCompile
  | s == EmacsMode.locateFlag  = add EmacsModeLocate
  | otherwise = throwError $ concat
     [ "unknown emacs-mode command "
     , s
     , " ("
     , printEmacsModeCommands "commands"
     , ")"
     ]
  where
    add m = return o{ optEmacsMode = Set.insert m $ optEmacsMode o }

printEmacsModeCommands :: String -> String
printEmacsModeCommands mvar = concat
  [ "available"
  , ifNull mvar "" {-else-} \ cmd -> " " ++ cmd
  , ": "
  , intercalate ", " emacsModeValues
  ]

safeFlag :: Flag PragmaOptions
safeFlag o = do
  return $ o { _optSafe        = Value True
             , _optSizedTypes  = setDefault False (_optSizedTypes o)
             }

syntacticEqualityFlag :: Maybe String -> Flag PragmaOptions
syntacticEqualityFlag s o =
  case fuel of
    Left err   -> throwError err
    Right fuel -> return $ o { _optSyntacticEquality = fuel }
  where
  fuel = case s of
    Nothing -> Right Strict.Nothing
    Just s  -> case readMaybe s of
      Just n | n >= 0 -> Right (Strict.Just n)
      _               -> Left $ "Not a natural number: " ++ s

ignoreInterfacesFlag :: Flag CommandLineOptions
ignoreInterfacesFlag o = return $ o { optIgnoreInterfaces = True }

ignoreAllInterfacesFlag :: Flag CommandLineOptions
ignoreAllInterfacesFlag o = return $ o { optIgnoreAllInterfaces = True }

noWriteInterfacesFlag :: Flag CommandLineOptions
noWriteInterfacesFlag o = return $ o { optWriteInterfaces = False }

traceImportsFlag :: Maybe String -> Flag CommandLineOptions
traceImportsFlag arg o = do
  mode <- case arg of
            Nothing -> return 2
            Just str -> case reads str :: [(Integer, String)] of
                          [(n, "")] -> return n
                          _ -> throwError $ "unknown printing option " ++ str ++ ". Please specify a number."
  return $ o { optTraceImports = mode }

diagnosticsColour :: Maybe String -> Flag CommandLineOptions
diagnosticsColour arg o = case arg of
  Just "auto"   -> pure o { optDiagnosticsColour = AutoColour }
  Just "always" -> pure o { optDiagnosticsColour = AlwaysColour }
  Just "never"  -> pure o { optDiagnosticsColour = NeverColour }
  Just str -> throwError $ "unknown colour option " ++ str ++ ". Please specify one of auto, always, or never."
  Nothing -> pure o { optDiagnosticsColour = AutoColour }

parallelismFlag :: Maybe String -> Flag CommandLineOptions
parallelismFlag (Just n) o = case readMaybe n of
  Just 0  -> pure o { optParallelChecking = Parallel Nothing }
  Just 1  -> pure o { optParallelChecking = Sequential }
  Just i  -> pure o { optParallelChecking = Parallel (Just i) }
  Nothing -> throwError $ "the parallelism should be a number, and " <> show n <> " isn't."
parallelismFlag Nothing o = pure o { optParallelChecking = Parallel Nothing }


-- | Side effect for setting '_optUseUnicode'.
--
unicodeOrAsciiEffect :: UnicodeOrAscii -> Flag PragmaOptions
unicodeOrAsciiEffect a o = return $ UNSAFE.unsafePerformIO $ do
  unsafeSetUnicodeOrAscii a
  return o

ghciInteractionFlag :: Flag CommandLineOptions
ghciInteractionFlag o = return $ o { optGHCiInteraction = True }

jsonInteractionFlag :: Flag CommandLineOptions
jsonInteractionFlag o = return $ o { optJSONInteraction = True }

interactionExitFlag :: Flag CommandLineOptions
interactionExitFlag o = return $ o { optExitOnError = True }

vimFlag :: Flag CommandLineOptions
vimFlag o = return $ o { optGenerateVimFile = True }

onlyScopeCheckingFlag :: Flag CommandLineOptions
onlyScopeCheckingFlag o = return $ o { optOnlyScopeChecking = True }

transliterateFlag :: Flag CommandLineOptions
transliterateFlag o = return $ o { optTransliterate = True }

mdOnlyAgdaBlocksFlag :: Bool -> Flag CommandLineOptions
mdOnlyAgdaBlocksFlag b o = return $ o { optMdOnlyAgdaBlocks = b }

withKFlag :: Flag PragmaOptions
withKFlag =
  -- with-K is the opposite of --without-K, so collapse default when disabling --without-K
  lensOptWithoutK (lensCollapseDefault $ const $ pure False)
  >=>
  -- with-K only restores any unsetting of --erased-matches, so keep its default
  lensOptErasedMatches (lensKeepDefault $ const $ pure True)


withoutKFlag :: Flag PragmaOptions
withoutKFlag o = return $ o
  { _optWithoutK                = Value True
  , _optFlatSplit               = setDefault False $ _optFlatSplit o
  , _optErasedMatches           = setDefault False $ _optErasedMatches o
  }

-- A unified flag for all cubical variants:
-- [--cubical] defaults to Cubical
-- [--cubical={compatible,no-glue,erased,full}] corresponds to the 4 options.
cubicalFlagOptArg :: Maybe String -> Flag PragmaOptions
cubicalFlagOptArg s = case s of
  Nothing           -> cubicalFlag CFull
  Just "full"       -> cubicalFlag CFull
  Just "erased"     -> cubicalFlag CErased
  Just "no-glue"    -> cubicalFlag CWithoutGlue
  Just "compatible" -> cubicalCompatibleFlag
  _ -> return $ throwError
    "Cubical variant can be omitted or one of {compatible, no-glue, erased, full}."

cubicalCompatibleFlag :: Flag PragmaOptions
cubicalCompatibleFlag o =
  return $ o
  { _optCubicalCompatible       = Value True
  , _optWithoutK                = setDefault True  $ _optWithoutK o
  , _optFlatSplit               = setDefault False $ _optFlatSplit o
  , _optErasedMatches           = setDefault False $ _optErasedMatches o
  }

cubicalFlag
  :: Cubical  -- ^ Which variant of Cubical Agda?
  -> Flag PragmaOptions
cubicalFlag variant o =
  return $ o
  { _optCubical                 = Just variant
  , _optCubicalCompatible       = setDefault True  $ _optCubicalCompatible o
  , _optWithoutK                = setDefault True  $ _optWithoutK o
  -- Andreas, 2026-01-20, issue #8326
  -- Do not set optTwoLevel here, but have been implied by optCubical
  -- , _optTwoLevel                = setDefault True  $ _optTwoLevel o
  , _optFlatSplit               = setDefault False $ _optFlatSplit o
  , _optErasedMatches           = setDefault False $ _optErasedMatches o
  }

instanceDepthFlag :: String -> Flag PragmaOptions
instanceDepthFlag s o = do
  d <- integerArgument "--instance-search-depth" s
  return $ o { _optInstanceSearchDepth = d }

inversionMaxDepthFlag :: String -> Flag PragmaOptions
inversionMaxDepthFlag s o = do
  d <- integerArgument "--inversion-max-depth" s
  return $ o { _optInversionMaxDepth = d }

interactiveFlag :: Flag CommandLineOptions
interactiveFlag  o = return $ o { optInteractive = True }

compileDirFlag :: FilePath -> Flag CommandLineOptions
compileDirFlag f o = return $ o { optCompileDir = Just f }

includeFlag :: FilePath -> Flag CommandLineOptions
includeFlag d o = return $ o { optIncludePaths = d : optIncludePaths o }

libraryFlag :: String -> Flag CommandLineOptions
libraryFlag s o = return $ o { optLibraries = optLibraries o ++ [parseLibName s] }

overrideLibrariesFileFlag :: String -> Flag CommandLineOptions
overrideLibrariesFileFlag s o =
  return $ o
    { optOverrideLibrariesFile = Just s
    , optUseLibs = True
    }

noDefaultLibsFlag :: Flag CommandLineOptions
noDefaultLibsFlag o = return $ o { optDefaultLibs = False }

noLibsFlag :: Flag CommandLineOptions
noLibsFlag o = return $ o { optUseLibs = False }

verboseFlag :: String -> Flag PragmaOptions
verboseFlag s o =
    do  (k,n) <- parseVerbose s
        return $
          o { _optVerbose =
                Strict.Just $ Trie.insert k n $
                case _optVerbose o of
                  Strict.Nothing -> Trie.singleton [] 1
                  Strict.Just v  -> v
            }
  where
    parseVerbose :: String -> OptM ([VerboseKeyItem], VerboseLevel)
    parseVerbose s = case parseVerboseKey s of
      []  -> usage
      s0:ss0 -> do
        let (ss, s) = initLast1 s0 ss0
        -- The last entry must be a number.
        n <- maybe usage return $ readMaybe $ toList s
        return (ss, n)
    usage = throwError "argument to verbose should be on the form x.y.z:N or N"

profileFlag :: String -> Flag PragmaOptions
profileFlag s o =
  case addProfileOption s (_optProfiling o) of
    Left err   -> throwError err
    Right prof -> pure o{ _optProfiling = prof }

warningModeFlag :: String -> Flag PragmaOptions
warningModeFlag s o = case warningModeUpdate s of
  Right upd -> return $ o { _optWarningMode = upd (_optWarningMode o) }
  Left err  -> o <$ tell1 (WarningProblem err)

terminationDepthFlag :: String -> Flag PragmaOptions
terminationDepthFlag s o =
    do k <- maybe usage return $ readMaybe s
       when (k < 1) $ usage -- or: turn termination checking off for 0
       return $ o { _optTerminationDepth = CutOff $ k-1 }
    where usage = throwError "argument to termination-depth should be >= 1"

confluenceCheckFlag :: ConfluenceCheck -> Flag PragmaOptions
confluenceCheckFlag f o = return $ o { _optConfluenceCheck = Just f }

noConfluenceCheckFlag :: Flag PragmaOptions
noConfluenceCheckFlag o = return $ o { _optConfluenceCheck = Nothing }

exactSplitFlag :: Bool -> Flag PragmaOptions
exactSplitFlag b o = do
  return $ conformWarningsToOption exactSplitWarnings (const b)
         $ o { _optExactSplit  = Value b }


integerArgument :: String -> String -> OptM Int
integerArgument flag s = maybe usage return $ readMaybe s
  where
  usage = throwError $ "option '" ++ flag ++ "' requires an integer argument"

-- | This list should contain all options defined in this module.
standardOptions :: [OptDescr (Flag CommandLineOptions)]
standardOptions = concat $
  map (fmap lensPragmaOptions) (snd latexPragmaOptions) :
  map snd optionGroups

optionGroups :: [(String, [OptDescr (Flag CommandLineOptions)])]
optionGroups =
  [ informationOptions
  , mainModeOptions
  , projectOptions
  , essentialConfigurationOptions
  , literateOptions
  , diagnosticsOptions
  , emb warningPragmaOptions
  , emb checkerPragmaOptions
  , emb languagePragmaOptions
  , emb universePragmaOptions
  , emb modalityPragmaOptions
  , emb terminationPragmaOptions
  , emb patternMatchingPragmaOptions
  , emb instancePragmaOptions
  , emb rewritingPragmaOptions
  , emb equalityCheckingPragmaOptions
  , emb optimizationPragmaOptions
  , emb printerPragmaOptions
  , emb backendPragmaOptions
  , compilationOptions
  , emb debuggingPragmaOptions
  , emb reflectionPragmaOptions
  ]
  where
    emb = second $ map $ fmap lensPragmaOptions

-- | Options that make Agda print information, setup itself etc.
--   Agda can execute these tasks in addition to a main mode \/ frontend \/ interactor.
informationOptions :: (String, [OptDescr (Flag CommandLineOptions)])
informationOptions = ("Setup and basic information",)
    [ Option ['V']  ["version"] (NoArg versionFlag)
                    ("print version information")

    , Option []     ["numeric-version"] (NoArg numericVersionFlag)
                    ("print version number")

    , Option ['?']  ["help"]    (OptArg helpFlag helpArg)
                    ("print help; " ++ printHelpTopics helpArg)

    , Option []     ["emacs-mode"] (ReqArg emacsModeFlag emacsModeArg) $ concat
                    [ "administer the Emacs Agda mode; "
                    , printEmacsModeCommands (emacsModeArg ++ "s")
                    , "; confer --help=emacs-mode"
                    ]

    , Option []     ["print-agda-dir"] (NoArg printAgdaDataDirFlag)
                    ("print the Agda data directory")

    , Option []     ["print-agda-app-dir"] (NoArg printAgdaAppDirFlag)
                    ("print $AGDA_DIR")

    , Option []     ["print-agda-data-dir"] (NoArg printAgdaDataDirFlag)
                    ("print the Agda data directory")

    , Option []     ["print-options"] (NoArg printOptionsFlag)
                    ("print the full list of Agda's options")

    , Option []     ["setup"] (NoArg setupFlag)
                    ("setup the Agda data directory")
    ]

mainModeOptions :: (String, [OptDescr (Flag CommandLineOptions)])
mainModeOptions = ("Main modes of operation",)
    [ Option []     ["build-library"] (NoArg \ o -> return o{ optBuildLibrary = True })
                    "build all modules included by the @.agda-lib@ file in the current directory"

    , Option ['I']  ["interactive"] (NoArg interactiveFlag)
                    "start in interactive mode"

    , Option []     ["interaction"] (NoArg ghciInteractionFlag)
                    "for use with the Emacs mode"
    , Option []     ["interaction-json"] (NoArg jsonInteractionFlag)
                    "for use with other editors such as Atom"
    ]

projectOptions :: (String, [OptDescr (Flag CommandLineOptions)])
projectOptions = ("Project configuration",)
    [ Option ['i']  ["include-path"] (ReqArg includeFlag "DIR")
                    "look for imports in DIR"
    , Option ['l']  ["library"] (ReqArg libraryFlag "LIB")
                    "use library LIB"
    , Option []     ["library-file"] (ReqArg overrideLibrariesFileFlag "FILE")
                    "use FILE instead of the standard libraries file"
    , Option []     ["no-libraries"] (NoArg noLibsFlag)
                    "don't use any library files"
    , Option []     ["no-default-libraries"] (NoArg noDefaultLibsFlag)
                    "don't use default libraries"
    ]

essentialConfigurationOptions :: (String, [OptDescr (Flag CommandLineOptions)])
essentialConfigurationOptions = ("Essential type checker configuration",)
    [ Option []     ["ignore-interfaces"] (NoArg ignoreInterfacesFlag)
                    "ignore interface files (re-type check everything)"
    , Option []     ["no-write-interfaces"] (NoArg noWriteInterfacesFlag)
                    "don't write interface files to the filesystem"

    , Option []     ["only-scope-checking"] (NoArg onlyScopeCheckingFlag)
                    "only scope-check the top-level module, do not type-check it"
    , Option []     ["interaction-exit-on-error"]
                    (NoArg interactionExitFlag)
                    "exit if a type error is encountered"
    , Option []     ["vim"] (NoArg vimFlag)
                    "generate Vim highlighting files"
    , Option ['j']  ["parallel"] (OptArg parallelismFlag "N")
                    "use N cores for parallel type-checking. The default is 1, 0 (or no argument) means auto."
    ]

literateOptions :: (String, [OptDescr (Flag CommandLineOptions)])
literateOptions = ("Literate Agda",)
    [ Option []     ["literate-markdown-only-agda-blocks"] (NoArg $ mdOnlyAgdaBlocksFlag True)
                    "in literate Markdown/Typst, only treat code blocks marked ```agda as Agda code"
    , Option []     ["no-literate-markdown-only-agda-blocks"] (NoArg $ mdOnlyAgdaBlocksFlag False)
                    "treat all code blocks as Agda code (default)"
    ]

diagnosticsOptions :: (String, [OptDescr (Flag CommandLineOptions)])
diagnosticsOptions = ("Diagnostics and output",) $
    [ Option []     ["colour", "color"] (OptArg diagnosticsColour (intercalate "|" colorValues))
                    ("whether or not to colour diagnostics output. The default is auto.")

    , Option []     ["trace-imports"] (OptArg traceImportsFlag traceImportsArg)
                    (concat
                      [ "print information about accessed modules during type-checking (where "
                      , traceImportsArg
                      , "="
                      , intercalate "|" traceImportsValues
                      , ", default: 2)"
                      ])

    , Option []     ["transliterate"] (NoArg transliterateFlag)
                    "transliterate unsupported code points when printing to stdout/stderr"
    ] ++ map (fmap lensPragmaOptions) (snd unicodePragmaOptions)

compilationOptions :: (String, [OptDescr (Flag CommandLineOptions)])
compilationOptions = ("Compilation options",) $
    [ Option []     ["compile-dir"] (ReqArg compileDirFlag "DIR")
                    ("directory for compiler output (default: the project root)")
    ] ++ map (fmap lensPragmaOptions) (snd compilationPragmaOptions)

-- | Command line options of previous versions of Agda.
--   Should not be listed in the usage info, put parsed by GetOpt for good error messaging.
deadStandardOptions :: [OptDescr (Flag CommandLineOptions)]
deadStandardOptions =
    [ removedOption "sharing"    msgSharing
    , removedOption "no-sharing" msgSharing
    , removedOption "local-interfaces" "(in 2.8.0)"
    , Option []     ["ignore-all-interfaces"] (NoArg ignoreAllInterfacesFlag) -- not deprecated! Just hidden
                    "ignore all interface files (re-type check everything, including builtin files)"
      -- https://github.com/agda/agda/issues/3522#issuecomment-461010898
      -- The option is "developer only", so it is hidden.
      -- However, it is documented in the user manual.
    ] ++ map (fmap lensPragmaOptions) deadPragmaOptions
  where
    msgSharing = "(in favor of the Agda abstract machine)"

-- | This list should contain all pragma options except for the 'deadPragmaOptions'.
pragmaOptions :: [OptDescr (Flag PragmaOptions)]
pragmaOptions = concat $ map snd
  [ unicodePragmaOptions
  , warningPragmaOptions
  , checkerPragmaOptions
  , languagePragmaOptions
  , universePragmaOptions
  , modalityPragmaOptions
  , terminationPragmaOptions
  , patternMatchingPragmaOptions
  , instancePragmaOptions
  , rewritingPragmaOptions
  , equalityCheckingPragmaOptions
  , optimizationPragmaOptions
  , printerPragmaOptions
  , latexPragmaOptions
  , backendPragmaOptions
  , compilationPragmaOptions
  , debuggingPragmaOptions
  , reflectionPragmaOptions
  ]

warningPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
warningPragmaOptions = ("Warnings",) $ concat
  [ [ Option ['W']  ["warning"] (ReqArg warningModeFlag warningArg)
                    ("set warning flags. See --help=warning.")
    ]
  ]

-- | Controlling extra checks (termination etc.).
checkerPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
checkerPragmaOptions = ("Consistency checking",) $ concat
  [ pragmaFlag      "allow-unsolved-metas" lensOptAllowUnsolved
                   "succeed and create interface file regardless of unsolved meta variables" ""
                    Nothing
  , pragmaFlag      "allow-incomplete-matches" lensOptAllowIncompleteMatch
                    "succeed and create interface file regardless of incomplete pattern matches" ""
                    Nothing
  , pragmaFlag      "positivity-check" lensOptPositivityCheck
                    "warn about not strictly positive data types" ""
                    Nothing
  , pragmaFlag      "termination-check" lensOptTerminationCheck
                    "warn about possibly nonterminating code" ""
                    Nothing
  , [ Option []     ["termination-depth"] (ReqArg terminationDepthFlag "N")
                    ("allow termination checker to count decrease/increase upto N (default N=" ++
                     show (1 + defaultCutOff) ++ ")")
    ]
  , [ Option []     ["safe"] (NoArg safeFlag)
                    "disable postulates, unsafe OPTION pragmas and primEraseEquality, implies --no-sized-types"
    ]
  , pragmaFlag      "allow-exec" lensOptAllowExec
                    "allow system calls to trusted executables with primExec" ""
                    Nothing
  ]

-- | Main flavor of language.
languagePragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
languagePragmaOptions = ("Language variant",)
    [ Option []     ["without-K"] (NoArg withoutKFlag)
                    "turn on checks to make code compatible with HoTT (e.g. disabling the K rule). Implies --no-flat-split."
    , Option []     ["cubical"] (OptArg cubicalFlagOptArg "VARIANT")
                    $ "enable cubical features (e.g. overloads lambdas for paths)." ++
                      "Accepted variants: full, erased, no-glue, compatible (default: full)."
    -- For backwards compatibility only. Use "--cubical=compatible" instead.
    , Option []     ["cubical-compatible"] (NoArg cubicalCompatibleFlag)
                    "turn on generation of auxiliary code required for --cubical, implies --without-K"
    -- For backwards compatibility only. Use "--cubical=erased" instead.
    , Option []     ["erased-cubical"] (NoArg $ cubicalFlag CErased)
                    "enable cubical features (some only in erased settings), implies --cubical=compatible"
    , Option []     ["with-K"] (NoArg withKFlag)
                    "enable the K rule in pattern matching (default)"
    ]

universePragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
universePragmaOptions = ("Universes",) $ concat
  [ pragmaFlag      "type-in-type" lensOptNoUniverseCheck
                    "ignore universe levels"  "(this makes Agda inconsistent)"
                    Nothing
  , pragmaFlag      "omega-in-omega" lensOptOmegaInOmega
                    "enable typing rule Setω : Setω" "(this makes Agda inconsistent)"
                    Nothing
  , pragmaFlag      "cumulativity" lensOptCumulativity
                    "enable subtyping of universes" "(e.g. Set =< Set₁)"
                    $ Just "disable subtyping of universes"
  , pragmaFlag      "prop" lensOptProp
                    "enable the use of the Prop universe" ""
                    $ Just "disable the use of the Prop universe"
  , pragmaFlag      "level-universe" lensOptLevelUniverse
                    "place type Level in a dedicated LevelUniv universe" ""
                    Nothing
  , pragmaFlag      "two-level" lensOptTwoLevel
                    "enable the use of SSet* universes" ""
                    Nothing
  , pragmaFlag      "universe-polymorphism" lensOptUniversePolymorphism
                    "enable universe polymorphism" ""
                    $ Just "disable universe polymorphism"
  , pragmaFlag      "large-indices" lensOptLargeIndices
                    "allow constructors with large indices" ""
                    $ Just "always check that constructor arguments live in universes compatible with that of the datatype"

  , pragmaFlag      "import-sorts" lensOptImportSorts
                    "implicitly import Agda.Primitive using (Set; Prop) at the start of each top-level module" ""
                    $ Just "disable the implicit import of Agda.Primitive using (Set; Prop) at the start of each top-level module"
  , pragmaFlag      "load-primitives" lensOptLoadPrimitives
                    "load primitives modules" ""
                    $ Just "disable loading of primitive modules completely (implies --no-import-sorts)"
  ]

modalityPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
modalityPragmaOptions = ("Modalities",) $ concat
  [ pragmaFlag      "erasure" lensOptErasure
                    "enable erasure" ""
                    Nothing
  , pragmaFlag      "erased-matches" lensOptErasedMatches
                    "allow matching in erased positions for single-constructor types" "(implies --erasure if supplied explicitly)"
                    Nothing
  , pragmaFlag      "erase-record-parameters" lensOptEraseRecordParameters
                    "mark all parameters of record modules as erased" "(implies --erasure)"
                    Nothing
  , pragmaFlag      "cohesion" lensOptCohesion
                    "enable the cohesion modalities" "(in particular @flat)"
                    Nothing
  , pragmaFlag      "flat-split" lensOptFlatSplit
                    "allow splitting on `(@flat x : A)' arguments" "(implies --cohesion)"
                    Nothing
  , pragmaFlag      "guarded" lensOptGuarded
                    "enable @lock/@tick attributes" ""
                    $ Just "disable @lock/@tick attributes"
  , pragmaFlag      "polarity" lensOptPolarity
                    "enable the polarity modalities (@++, @mixed, etc.) and their integration in the positivity checker" ""
                    Nothing
  , pragmaFlag      "occurrence-analysis" lensOptOccurrence
                    "enable automated occurrence analysis for functions"
                    "(can be slow)"
                    Nothing
  , pragmaFlag      "irrelevant-projections" lensOptIrrelevantProjections
                    "enable projection of irrelevant record fields and similar irrelevant definitions" "(inconsistent)"
                    $ Just "disable projection of irrelevant record fields and similar irrelevant definitions"
  , pragmaFlag      "experimental-irrelevance" lensOptExperimentalIrrelevance
                    "enable potentially unsound irrelevance features" "(irrelevant levels, irrelevant data matching)"
                    Nothing
  ]

terminationPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
terminationPragmaOptions = ("Termination and productivity checking",) $ concat
  [ pragmaFlag      "sized-types" lensOptSizedTypes
                    "enable sized types" "(inconsistent with --guardedness)"
                    $ Just "disable sized types"
  , pragmaFlag      "guardedness" lensOptGuardedness
                    "enable constructor-based guarded corecursion" "(inconsistent with --sized-types)"
                    $ Just "disable constructor-based guarded corecursion"
  , pragmaFlag      "forced-argument-recursion" lensOptForcedArgumentRecursion
                    "allow recursion on forced constructor arguments" ""
                    Nothing
  ]

patternMatchingPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
patternMatchingPragmaOptions = ("Pattern matching",) $ concat
  [ pragmaFlag      "pattern-matching" lensOptPatternMatching
                    "enable pattern matching" ""
                    $ Just "disable pattern matching completely"
  , pragmaFlag      "copatterns" lensOptCopatterns
                    "enable definitions by copattern matching" ""
                    $ Just "disable definitions by copattern matching"
  , [ Option []     ["exact-split"] (NoArg $ exactSplitFlag True)
                    "require all clauses in a definition to hold as definitional equalities (unless marked CATCHALL)"
    , Option []     ["no-exact-split"] (NoArg $ exactSplitFlag False)
                    "do not require all clauses in a definition to hold as definitional equalities (default)"
    ]
  , pragmaFlag      "hidden-argument-puns" lensOptHiddenArgumentPuns
                    "interpret the patterns {x} and {{x}} as puns" ""
                    Nothing
  , pragmaFlag      "injective-type-constructors" lensOptInjectiveTypeConstructors
                    "enable injective type constructors" "(makes Agda anti-classical and possibly inconsistent)"
                    $ Just "disable injective type constructors"
  , [ Option []     ["inversion-max-depth"] (ReqArg inversionMaxDepthFlag "N")
                    "set maximum depth for pattern match inversion to N (default: 50)"
    ]
  ]

instancePragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
instancePragmaOptions = ("Instance search",) $ concat
  [ [ Option []     ["instance-search-depth"] (ReqArg instanceDepthFlag "N")
                    "set instance search depth to N (default: 500)"
    ]
  , backtrackingInstancesOption
  , pragmaFlag      "qualified-instances" lensOptQualifiedInstances
                    "use instances with qualified names" ""
                    Nothing
  , pragmaFlag      "experimental-lazy-instances" lensOptExperimentalLazyInstances
                    "enable experimental, faster implementation of instance search" ""
                    Nothing
  ]

rewritingPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
rewritingPragmaOptions = ("Rewriting and confluence",) $ concat
  [ pragmaFlag      "rewriting" lensOptRewriting
                    "enable declaration and use of REWRITE rules" ""
                    $ Just "disable declaration and use of REWRITE rules"
  , [ Option []     ["local-confluence-check"] (NoArg $ confluenceCheckFlag LocalConfluenceCheck)
                    "enable checking of local confluence of REWRITE rules"
    , Option []     ["confluence-check"] (NoArg $ confluenceCheckFlag GlobalConfluenceCheck)
                    "enable global confluence checking of REWRITE rules (more restrictive than --local-confluence-check)"
    , Option []     ["no-confluence-check"] (NoArg noConfluenceCheckFlag)
                    "disable confluence checking of REWRITE rules (default)"
    ]
  , pragmaFlag      "local-rewriting" lensOptLocalRewriting
                    "enable declaring local rewrite rules with the @rew annotation" ""
                    $ Just "disable local rewrite rules"
  ]

equalityCheckingPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
equalityCheckingPragmaOptions = ("Definitional equality",) $ concat
  [ pragmaFlag      "eta-equality" lensOptEta
                    "default records to eta-equality" ""
                    $ Just "default records to no-eta-equality"
  , lossyUnificationOption
  , requireUniqueMetaSolutionsOptions
  , [ Option []     ["no-syntactic-equality"] (NoArg $ syntacticEqualityFlag (Just "0"))
                    "disable the syntactic equality shortcut in the conversion checker"
    , Option []     ["syntactic-equality"] (OptArg syntacticEqualityFlag "FUEL")
                    "give the syntactic equality shortcut FUEL units of fuel (default: unlimited)"
    ]
  , pragmaFlag      "auto-inline" lensOptAutoInline
                    "enable automatic compile-time inlining" ""
                    $ Just "disable automatic compile-time inlining, only definitions marked INLINE will be inlined"

  , pragmaFlag      "fast-reduce" lensOptFastReduce
                    "enable reduction using the Agda Abstract Machine" ""
                    $ Just "disable reduction using the Agda Abstract Machine"
  , pragmaFlag      "call-by-name" lensOptCallByName
                    "use call-by-name evaluation instead of call-by-need" ""
                    $ Just "use call-by-need evaluation"
  ]

optimizationPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
optimizationPragmaOptions = ("Type checker optimizations",) $ concat
  [ pragmaFlag      "caching" lensOptCaching
                    "enable caching of typechecking" ""
                    $ Just "disable caching of typechecking"
  , pragmaFlag      "double-check" lensOptDoubleCheck
                    "enable double-checking of all terms using the internal typechecker" ""
                    $ Just "disable double-checking of terms"
  , pragmaFlag      "forcing" lensOptForcing
                    "enable the forcing analysis for data constructors" "(optimisation)"
                    $ Just "disable the forcing analysis"
  , pragmaFlag      "projection-like" lensOptProjectionLike
                    "enable the analysis whether function signatures liken those of projections" "(optimisation)"
                    $ Just "disable the projection-like analysis"
  , pragmaFlag      "infer-absurd-clauses" lensOptInferAbsurdClauses
                    "eliminate absurd clauses in case splitting and coverage checking" ""
                    $ Just "do not automatically eliminate absurd clauses in case splitting and coverage checking (can speed up type-checking)"
  , pragmaFlag      "save-metas" lensOptSaveMetas
                    "save meta-variables" ""
                    Nothing
  ]

unicodePragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
unicodePragmaOptions = ("Unicode",) $ concat
  [ pragmaFlag'     "unicode" lensOptUseUnicode unicodeOrAsciiEffect
                    "use unicode characters when printing terms" ""
                    Nothing
  ]

-- | Controlling the rendering of Agda expressions.
printerPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
printerPragmaOptions = ("Checker output",) $ concat
  [ pragmaFlag      "show-implicit" lensOptShowImplicit
                    "show implicit arguments when printing" ""
                    Nothing
  , pragmaFlag      "show-irrelevant" lensOptShowIrrelevant
                    "show irrelevant arguments when printing" ""
                    Nothing
  , pragmaFlag      "show-identity-substitutions" lensOptShowIdentitySubstitutions
                    "show all arguments of metavariables when printing terms" ""
                    Nothing
  , pragmaFlag      "print-pattern-synonyms" lensOptPrintPatternSynonyms
                    "keep pattern synonyms when printing terms" ""
                    $ Just "expand pattern synonyms when printing terms"
  , pragmaFlag      "postfix-projections" lensOptPostfixProjections
                    "prefer postfix projection notation" ""
                    $ Just "prefer prefix projection notation"
  , pragmaFlag      "keep-pattern-variables" lensOptKeepPatternVariables
                    "don't replace variables with dot patterns during case splitting" ""
                    $ Just "replace variables with dot patterns during case splitting"
  ]

-- | Latex pragma options.
latexPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
latexPragmaOptions = ("Latex options",) $ concat
  [ pragmaFlag      "count-clusters" lensOptCountClusters
                    "count extended grapheme clusters when generating LaTeX"
                    ("(note that this flag " ++
#ifdef COUNT_CLUSTERS
                      "is not enabled in all builds"
#else
                      "has not been enabled in this build"
#endif
                      ++ " of Agda)")
                    Nothing
  ]

-- | Backend-relevant options.
backendPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
backendPragmaOptions = ("Backend options",) $ concat
  [ pragmaFlag      "keep-covering-clauses" lensOptKeepCoveringClauses
                    "do not discard covering clauses" "(required for some external backends)"
                    $ Just "discard covering clauses"
  ]

-- | Common options for compilers.
compilationPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
compilationPragmaOptions = ("Compilation options",) $ concat
  [ pragmaFlag      "main" lensOptCompileMain
                    "treat the requested module as the main module of a program when compiling" ""
                    Nothing
  ]

-- | Debugging and profiling Agda.
debuggingPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
debuggingPragmaOptions = ("Debugging and profiling Agda",) $ concat
  [ [ Option ['v']  ["verbose"] (ReqArg verboseFlag "N")
                    "set verbosity level to N. Only has an effect if Agda was built with the \"debug\" flag."
    , Option []     ["profile"] (ReqArg profileFlag profileArg)
                    (concat
                       [ "turn on profiling for "
                       , profileArg
                       , " (where "
                       , profileArg
                       , "="
                       , intercalate "|" profileValues
                       , ")"
                       ])
    ]
  ]

reflectionPragmaOptions :: (String, [OptDescr (Flag PragmaOptions)])
reflectionPragmaOptions = ("Reflection",) $ concat
  [ pragmaFlag "quote-metas" lensOptQuoteMetas
               "allow unquoting to not get blocked by metas" ""
               Nothing
  ]

-- | Construct a flag of type @WithDefault _@
--
pragmaFlag :: (IsBool a, KnownBool b)
  => String
       -- ^ Long option name.  Prepended with @no-@ for negative version.
  -> Lens' PragmaOptions (WithDefault' a b)
       -- ^ Field to switch.
  -> String
       -- ^ Explanation for positive option.
  -> String
       -- ^ Additional info for positive option (not repeated for negative option).
  -> Maybe String
       -- ^ Explanation for negative option.
  -> [OptDescr (Flag PragmaOptions)]
pragmaFlag long field = pragmaFlag' long field (const return)

-- | Construct a flag of type @WithDefault _@
--
pragmaFlag' :: (IsBool a, KnownBool b)
  => String
       -- ^ Long option name.  Prepended with @no-@ for negative version.
  -> Lens' PragmaOptions (WithDefault' a b)
       -- ^ Field to switch.
  -> (a -> Flag PragmaOptions)
       -- ^ Given the new value, perform additional effect (can override field setting).
  -> String
       -- ^ Explanation for positive option.
  -> String
       -- ^ Additional info for positive option (not repeated for negative option).
  -> Maybe String
       -- ^ Explanation for negative option.
  -> [OptDescr (Flag PragmaOptions)]
       -- ^ Pair of option descriptors (positive, negative)
pragmaFlag' long field = pragmaFlagBool' long (field . lensCollapseDefault)

-- | Construct a flag of type 'IsBool'.
--
pragmaFlagBool :: (IsBool a)
  => String
       -- ^ Long option name.  Prepended with @no-@ for negative version.
  -> Lens' PragmaOptions a
       -- ^ Field to switch.
  -> String
       -- ^ Explanation for positive option.
  -> String
       -- ^ Additional info for positive option (not repeated for negative option).
  -> Maybe String
       -- ^ Explanation for negative option.
  -> [OptDescr (Flag PragmaOptions)]
pragmaFlagBool long field = pragmaFlagBool' long field (const return)

-- | Construct a flag of type 'IsBool' with extra effect.
--
pragmaFlagBool' :: IsBool a
  => String
       -- ^ Long option name.  Prepended with @no-@ for negative version.
  -> Lens' PragmaOptions a
       -- ^ Field to switch.
  -> (a -> Flag PragmaOptions)
       -- ^ Given the new value, perform additional effect (can override field setting).
  -> String
       -- ^ Explanation for positive option.
  -> String
       -- ^ Additional info for positive option (not repeated for negative option).
  -> Maybe String
       -- ^ Explanation for negative option.
  -> [OptDescr (Flag PragmaOptions)]
       -- ^ Pair of option descriptors (positive, negative)
pragmaFlagBool' long field effect pos info neg =
  [ Option [] [no b long] (flag b) (def b $ expl b) | b <- [True,False] ]
  where
  b0     = defaultPragmaOptions ^. field
  no   b = applyUnless b ("no-" ++)
  flag b = NoArg $ effect a . set field a
    where a = fromBool b
  def  b = applyWhen (fromBool b == b0) (++ " (default)")
  expl b = if b then unwords1 [pos, info] else fromMaybe ("do not " ++ pos) neg

pragmaOptionDefault :: KnownBool b => (PragmaOptions -> WithDefault b) -> Bool -> String
pragmaOptionDefault f b =
  if b == collapseDefault (f defaultPragmaOptions) then " (default)" else ""

lossyUnificationOption :: [OptDescr (Flag PragmaOptions)]
lossyUnificationOption =
  pragmaFlag "lossy-unification" lensOptFirstOrder
    "enable heuristically unifying `f es = f es'` by unifying `es = es'`"
    "even when it could lose solutions"
    Nothing

requireUniqueMetaSolutionsOptions :: [OptDescr (Flag PragmaOptions)]
requireUniqueMetaSolutionsOptions =
  pragmaFlag "require-unique-meta-solutions" lensOptRequireUniqueMetaSolutions
    "require unique solutions to meta variables"
    "even when it could lose solutions"
    Nothing

backtrackingInstancesOption :: [OptDescr (Flag PragmaOptions)]
backtrackingInstancesOption =
  pragmaFlag "backtracking-instance-search" lensOptBacktrackingInstances
    "allow backtracking during instance search"
    ""
    Nothing

-- | Pragma options of previous versions of Agda.
--   Should not be listed in the usage info, put parsed by GetOpt for good error messaging.
deadPragmaOptions :: [OptDescr (Flag PragmaOptions)]
deadPragmaOptions = concat
  [ map (uncurry removedOption)
    [ ("guardedness-preserving-type-constructors"
      , "")
    , ("no-coverage-check"
      , inVersion "2.5.1") -- see issue #1918
    , ("no-sort-comparison"
      , "")
    , ("subtyping"
      , inVersion "2.6.3") -- see issue #5427
    , ("no-subtyping"
      , inVersion "2.6.3") -- see issue #5427
    , ("no-flat-split", inVersion "2.6.3")  -- See issue #6263.
    ]
  , map (uncurry renamedNoArgOption)
    [ ( "experimental-lossy-unification"
      , headWithDefault __IMPOSSIBLE__ lossyUnificationOption
      )
    , ( "overlapping-instances"
      , headWithDefault __IMPOSSIBLE__ backtrackingInstancesOption
      )
    ]
  ]
  where
    inVersion = ("in version " ++)

-- | Generate a dead options that just error out saying this option has been removed.
removedOption ::
     String
       -- ^ The name of the removed option.
  -> String
       -- ^ Optional: additional remark, like in which version the option was removed.
  -> OptDescr (Flag a)
removedOption name remark = Option [] [name] (NoArg $ const $ throwError msg) msg
  where
  msg = unwords ["Option", "--" ++ name, "has been removed", remark]

-- | Generate a deprecated option that resolves to another option.
renamedNoArgOption ::
     String
       -- ^ The deprecated long option name.
  -> OptDescr (Flag a)
       -- ^ The new option.
  -> OptDescr (Flag a)
       -- ^ The old option which additionally emits a 'RenamedOption' warning.
renamedNoArgOption old = \case
  Option _ [new] (NoArg flag) description ->
    Option [] [old] (NoArg flag') $ concat [description, " (DEPRECATED, use --", new, ")"]
    where
    flag' o = tell1 (OptionRenamed old new) >> flag o
  _ -> __IMPOSSIBLE__

-- | Used for printing usage info.
--   Does not include the dead options.
standardOptions_ :: [OptDescr ()]
standardOptions_ = map void standardOptions

-- | Simple interface for Agda.Utils.GetOpt
--   Could be moved to Agda.Utils.Options (does not exist yet)
getOptSimple
  :: [String]               -- ^ command line argument words
  -> [OptDescr (Flag opts)] -- ^ options handlers
  -> (String -> Flag opts)  -- ^ handler of non-options (only one is allowed)
  -> Flag opts              -- ^ combined opts data structure transformer
getOptSimple argv opts fileArg = \ defaults ->
  case getOpt' (ReturnInOrder fileArg) opts argv of
    (o, _, []          , [] )  -> foldl (>>=) (return defaults) o
    (_, _, unrecognized, errs) -> throwError $ umsg ++ emsg

      where
      ucap = "Unrecognized " ++ String.pluralS unrecognized "option" ++ ":"
      ecap = String.pluralS errs "Option error" ++ ":"
      umsg = if null unrecognized then "" else unlines $
       ucap : map suggest unrecognized
      emsg = if null errs then "" else unlines $
       ecap : errs

      -- Suggest alternatives that are at most 3 typos away

      longopts :: [String]
      longopts = map ("--" ++) $ concatMap (\ (Option _ long _ _) -> long) opts

      dist :: String -> String -> Int
      dist s t = restrictedDamerauLevenshteinDistance defaultEditCosts s t

      close :: String -> String -> Maybe (Int, String)
      close s t = let d = dist s t in if d <= 3 then Just (d, t) else Nothing

      closeopts :: String -> [(Int, String)]
      closeopts s = mapMaybe (close s) longopts

      alts :: String -> [List1 String]
      alts s = map (fmap snd) $ List1.groupOn fst $ closeopts s

      suggest :: String -> String
      suggest s = case alts s of
        []     -> s
        as : _ -> s ++ " (did you mean " ++ sugs as ++ " ?)"

      sugs :: List1 String -> String
      sugs (a :| []) = a
      sugs as  = "any of " ++ List1.unwords as

-- | Parse options from an options pragma.
parsePragmaOptions
  :: OptionsPragma
     -- ^ Pragma options.
  -> CommandLineOptions
     -- ^ Command-line options which should be updated.
  -> OptM PragmaOptions
parsePragmaOptions argv opts = do
  ps <- getOptSimple
          (pragmaStrings argv)
          (deadPragmaOptions ++ pragmaOptions)
          (\s _ -> throwError $ "Bad option in pragma: " ++ s)
          (optPragmaOptions opts)
  checkPragmaOptions ps

-- | Parse options for a plugin.
parsePluginOptions :: [String] -> [OptDescr (Flag opts)] -> Flag opts
parsePluginOptions argv opts =
  getOptSimple argv opts
    (\s _ -> throwError $
               "Internal error: Flag " ++ s ++ " passed to a plugin")

-- | Removes RTS options from a list of options.

stripRTS :: [String] -> [String]
stripRTS [] = []
stripRTS ("--RTS" : argv) = argv
stripRTS (arg : argv)
  | is "+RTS" arg = stripRTS $ drop 1 $ dropWhile (not . is "-RTS") argv
  | otherwise     = arg : stripRTS argv
  where
    is x arg = [x] == take 1 (words arg)
