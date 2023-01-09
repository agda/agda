{-# LANGUAGE CPP       #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PartialTypeSignatures #-}

{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Agda.Interaction.Options.Base
    ( CommandLineOptions(..)
    , PragmaOptions(..)
    , OptionError
    , OptionWarning(..), optionWarningName
    , Flag, OptM, runOptM, OptDescr(..), ArgDescr(..)
    , Verbosity, VerboseKey, VerboseLevel
    , WarningMode(..)
    , ConfluenceCheck(..)
    , PrintAgdaVersion(..)
    , UnicodeOrAscii(..)
    , DiagnosticsColours(..)
    , checkOpts
    , parsePragmaOptions
    , parsePluginOptions
    , parseVerboseKey
    , stripRTS
    , defaultOptions
    , defaultInteractionOptions
    , defaultCutOff
    , defaultPragmaOptions
    , standardOptions_
    , unsafePragmaOptions
    , recheckBecausePragmaOptionsChanged
    , InfectiveCoinfective(..)
    , InfectiveCoinfectiveOption(..)
    , infectiveCoinfectiveOptions
    , ImpliedPragmaOption(..)
    , impliedPragmaOptions
    , safeFlag
    , mapFlag
    , usage
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
    , optImportSorts
    , optLoadPrimitives
    , optAllowExec
    , optSaveMetas
    , optShowIdentitySubstitutions
    , optKeepCoveringClauses
    , optLargeIndices
    , optForcedArgumentRecursion
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
import Control.Monad        ( (>=>), when, unless, void )
import Control.Monad.Except ( ExceptT, MonadError(throwError), runExceptT )
import Control.Monad.Writer ( Writer, runWriter, MonadWriter(..) )

import Data.Function            ( (&) )
import Data.List                ( intercalate )
import Data.Maybe
import Data.Map                 ( Map )
import qualified Data.Map as Map
import Data.Set                 ( Set )
import qualified Data.Set as Set

import GHC.Generics (Generic)

import System.Console.GetOpt    ( getOpt', usageInfo, ArgOrder(ReturnInOrder)
                                , OptDescr(..), ArgDescr(..)
                                )
import qualified System.IO.Unsafe as UNSAFE (unsafePerformIO)

import Text.EditDistance
import Text.Read                ( readMaybe )

import Agda.Termination.CutOff  ( CutOff(..), defaultCutOff )

import Agda.Interaction.Library ( ExeName, LibName, OptionsPragma(..) )
import Agda.Interaction.Options.Help
  ( Help(HelpFor, GeneralHelp)
  , string2HelpTopic
  , allHelpTopics
  , helpTopicUsage
  )
import Agda.Interaction.Options.Warnings
import Agda.Syntax.Concrete.Glyph ( unsafeSetUnicodeOrAscii, UnicodeOrAscii(..) )
import Agda.Syntax.Common (Cubical(..))
import Agda.Syntax.Common.Pretty
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)

import Agda.Utils.Boolean
import Agda.Utils.FileName      ( AbsolutePath )
import Agda.Utils.Function      ( applyWhen, applyUnless )
import Agda.Utils.Functor       ( (<&>) )
import Agda.Utils.Lens          ( Lens', (^.), over, set )
import Agda.Utils.List          ( headWithDefault, initLast1 )
import Agda.Utils.List1         ( List1, String1, pattern (:|), toList )
import qualified Agda.Utils.List1        as List1
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad         ( tell1 )
import Agda.Utils.Null
import Agda.Utils.ProfileOptions
import Agda.Utils.String        ( unwords1 )
import qualified Agda.Utils.String       as String
import Agda.Utils.Trie          ( Trie )
import qualified Agda.Utils.Trie as Trie
import Agda.Utils.TypeLits
import Agda.Utils.WithDefault

import Agda.Utils.Impossible

import Agda.Version

-- OptDescr is a Functor --------------------------------------------------

type VerboseKey     = String
type VerboseKeyItem = String1
type VerboseLevel   = Int
-- | 'Strict.Nothing' is used if no verbosity options have been given,
-- thus making it possible to handle the default case relatively
-- quickly. Note that 'Strict.Nothing' corresponds to a trie with
-- verbosity level 1 for the empty path.
type Verbosity = Strict.Maybe (Trie VerboseKeyItem VerboseLevel)

parseVerboseKey :: VerboseKey -> [VerboseKeyItem]
parseVerboseKey = List1.wordsBy (`elem` ['.', ':'])

data DiagnosticsColours
  = AlwaysColour
  | NeverColour
  | AutoColour
  deriving (Show, Generic)

instance NFData DiagnosticsColours

-- Don't forget to update
--   doc/user-manual/tools/command-line-options.rst
-- if you make changes to the command-line options!

data CommandLineOptions = Options
  { optProgramName           :: String
  , optInputFile             :: Maybe FilePath
  , optIncludePaths          :: [FilePath]
  , optAbsoluteIncludePaths  :: [AbsolutePath]
      -- ^ The list should not contain duplicates.
  , optLibraries             :: [LibName]
  , optOverrideLibrariesFile :: Maybe FilePath
      -- ^ Use this (if 'Just') instead of @~\/.agda\/libraries@.
  , optDefaultLibs           :: Bool
       -- ^ Use @~\/.agda\/defaults@.
  , optUseLibs               :: Bool
       -- ^ look for @.agda-lib@ files.
  , optTraceImports          :: Integer
       -- ^ Configure notifications about imported modules.
  , optTrustedExecutables    :: Map ExeName FilePath
       -- ^ Map names of trusted executables to absolute paths.
  , optPrintAgdaDataDir      :: Bool
  , optPrintAgdaAppDir       :: Bool
  , optPrintVersion          :: Maybe PrintAgdaVersion
  , optPrintHelp             :: Maybe Help
  , optInteractive           :: Bool
      -- ^ Agda REPL (@-I@).
  , optGHCiInteraction       :: Bool
  , optJSONInteraction       :: Bool
  , optExitOnError           :: !Bool
      -- ^ Exit if an interactive command fails.
  , optCompileDir            :: Maybe FilePath
      -- ^ In the absence of a path the project root is used.
  , optGenerateVimFile       :: Bool
  , optIgnoreInterfaces      :: Bool
  , optIgnoreAllInterfaces   :: Bool
  , optLocalInterfaces       :: Bool
  , optPragmaOptions         :: PragmaOptions
  , optOnlyScopeChecking     :: Bool
      -- ^ Should the top-level module only be scope-checked, and not type-checked?
  , optTransliterate         :: Bool
      -- ^ Should code points that are not supported by the locale be transliterated?
  , optDiagnosticsColour     :: DiagnosticsColours
      -- ^ Configure colour output.
  }
  deriving (Show, Generic)

instance NFData CommandLineOptions

-- | Options which can be set in a pragma.

data PragmaOptions = PragmaOptions
  { _optShowImplicit              :: WithDefault 'False
  , _optShowGeneralized           :: WithDefault 'True
      -- ^ Show generalized parameters in Pi types
  , _optShowIrrelevant            :: WithDefault 'False
  , _optUseUnicode                :: WithDefault' UnicodeOrAscii 'True -- Would like to write UnicodeOk instead of True here
  , _optVerbose                   :: !Verbosity
  , _optProfiling                 :: ProfileOptions
  , _optProp                      :: WithDefault 'False
  , _optLevelUniverse             :: WithDefault 'False
  , _optTwoLevel                  :: WithDefault 'False
  , _optAllowUnsolved             :: WithDefault 'False
  , _optAllowIncompleteMatch      :: WithDefault 'False
  , _optPositivityCheck           :: WithDefault 'True
  , _optTerminationCheck          :: WithDefault 'True
  , _optTerminationDepth          :: CutOff
      -- ^ Cut off structural order comparison at some depth in termination checker?
  , _optUniverseCheck             :: WithDefault 'True
  , _optOmegaInOmega              :: WithDefault 'False
  , _optCumulativity              :: WithDefault 'False
  , _optSizedTypes                :: WithDefault 'False
  , _optGuardedness               :: WithDefault 'False
  , _optInjectiveTypeConstructors :: WithDefault 'False
  , _optUniversePolymorphism      :: WithDefault 'True
  , _optIrrelevantProjections     :: WithDefault 'False
      -- off by default in > 2.5.4, see issue #2170
  , _optExperimentalIrrelevance   :: WithDefault 'False
      -- ^ irrelevant levels, irrelevant data matching
  , _optWithoutK                  :: WithDefault 'False
  , _optCubicalCompatible         :: WithDefault 'False
  , _optCopatterns                :: WithDefault 'True
      -- ^ Allow definitions by copattern matching?
  , _optPatternMatching           :: WithDefault 'True
      -- ^ Is pattern matching allowed in the current file?
  , _optExactSplit                :: WithDefault 'False
  , _optHiddenArgumentPuns        :: WithDefault 'False
      -- ^ Should patterns of the form @{x}@ or @⦃ x ⦄@ be interpreted as puns?
  , _optEta                       :: WithDefault 'True
  , _optForcing                   :: WithDefault 'True
      -- ^ Perform the forcing analysis on data constructors?
  , _optProjectionLike            :: WithDefault 'True
      -- ^ Perform the projection-likeness analysis on functions?
  , _optErasure                   :: WithDefault 'False
  , _optErasedMatches             :: WithDefault 'True
      -- ^ Allow matching in erased positions for single-constructor,
      -- non-indexed data/record types. (This kind of matching is always
      -- allowed for record types with η-equality.)
  , _optEraseRecordParameters     :: WithDefault 'False
      -- ^ Mark parameters of record modules as erased?
  , _optRewriting                 :: WithDefault 'False
      -- ^ Can rewrite rules be added and used?
  , _optCubical                   :: Maybe Cubical
  , _optGuarded                   :: WithDefault 'False
  , _optFirstOrder                :: WithDefault 'False
      -- ^ Should we speculatively unify function applications as if they were injective? Implies
      --   optRequireUniqueMetaSolutions.
  , _optRequireUniqueMetaSolutions :: WithDefault 'True
      -- ^ Forbid non-unique meta solutions allowed. For instance from INJECTIVE_FOR_INFERENCE pragmas.
  , _optPostfixProjections        :: WithDefault 'True
      -- ^ Should system generated projections 'ProjSystem' be printed
      --   postfix (True) or prefix (False).
  , _optKeepPatternVariables      :: WithDefault 'True
      -- ^ Should case splitting replace variables with dot patterns
      --   (False) or keep them as variables (True).
  , _optInferAbsurdClauses        :: WithDefault 'True
      -- ^ Should case splitting and coverage checking try to discharge absurd clauses?
      --   Default: 'True', but 'False' might make coverage checking considerably faster in some cases.
  , _optInstanceSearchDepth       :: Int
  , _optBacktrackingInstances     :: WithDefault 'False
  , _optQualifiedInstances        :: WithDefault 'True
      -- ^ Should instance search consider instances with qualified names?
  , _optInversionMaxDepth         :: Int
  , _optSafe                      :: WithDefault 'False
  , _optDoubleCheck               :: WithDefault 'False
  , _optSyntacticEquality         :: !(Strict.Maybe Int)
    -- ^ Should the conversion checker use the syntactic equality
    -- shortcut? 'Nothing' means that it should. @'Just' n@, for a
    -- non-negative number @n@, means that syntactic equality checking
    -- gets @n@ units of fuel. If the fuel becomes zero, then
    -- syntactic equality checking is turned off. The fuel counter is
    -- decreased in the failure continuation of
    -- 'Agda.TypeChecking.SyntacticEquality.checkSyntacticEquality'.
  , _optWarningMode               :: WarningMode
  , _optCompileMain               :: WithDefault 'True
    -- ^ Treat the module given at the command line or via interaction as main module in compilation?
  , _optCaching                   :: WithDefault 'True
  , _optCountClusters             :: WithDefault 'False
    -- ^ Count extended grapheme clusters rather than code points
    --   when generating LaTeX.
  , _optAutoInline                :: WithDefault 'False
    -- ^ Automatic compile-time inlining for simple definitions
    --   (unless marked @NOINLINE@).
  , _optPrintPatternSynonyms      :: WithDefault 'True
  , _optFastReduce                :: WithDefault 'True
      -- ^ Use the Agda abstract machine ('fastReduce')?
  , _optCallByName                :: WithDefault 'False
      -- ^ Use call-by-name instead of call-by-need.
  , _optConfluenceCheck           :: Maybe ConfluenceCheck
      -- ^ Check confluence of rewrite rules?
  , _optCohesion                  :: WithDefault 'False
      -- ^ Are the cohesion modalities available?
  , _optFlatSplit                 :: WithDefault 'False
      -- ^ Can we split on a @(\@flat x : A)@ argument?
  , _optPolarity                  :: WithDefault 'False
      -- ^ Can we use modal polarities (@++, @+, etc.)?
  , _optImportSorts               :: WithDefault 'True
      -- ^ Should every top-level module start with an implicit statement
      --   @open import Agda.Primitive using (Set; Prop)@?
  , _optLoadPrimitives            :: WithDefault 'True
      -- ^ Should we load the primitive modules at all?
      --   This is a stronger form of 'optImportSorts'.
  , _optAllowExec                 :: WithDefault 'False
      -- ^ Allow running external @executables@ from meta programs.
  , _optSaveMetas                 :: WithDefault 'False
      -- ^ Save meta-variables to interface files.
  , _optShowIdentitySubstitutions :: WithDefault 'False
      -- ^ Show identity substitutions when pretty-printing terms
      --   (i.e. always show all arguments of a metavariable).
  , _optKeepCoveringClauses       :: WithDefault 'False
      -- ^ Do not discard clauses constructed by the coverage checker
      --   (needed for some external backends).
  , _optLargeIndices              :: WithDefault 'False
      -- ^ Allow large indices, and large forced arguments in
      -- constructors.
  , _optForcedArgumentRecursion   :: WithDefault 'True
      -- ^ Allow recursion on forced constructor arguments.
  }
  deriving (Show, Eq, Generic)

instance NFData PragmaOptions

data ConfluenceCheck
  = LocalConfluenceCheck
  | GlobalConfluenceCheck
  deriving (Show, Eq, Generic)

instance NFData ConfluenceCheck

-- | Options @--version@ and @--numeric-version@ (last wins).
data PrintAgdaVersion
  = PrintAgdaVersion
      -- ^ Print Agda version information and exit.
  | PrintAgdaNumericVersion
      -- ^ Print Agda version number and exit.
  deriving (Show, Generic)

instance NFData PrintAgdaVersion

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
-- --no-load-primitives implies --no-import-sorts
optImportSorts               = collapseDefault . _optImportSorts   && optLoadPrimitives
optLoadPrimitives            = collapseDefault . _optLoadPrimitives
optAllowExec                 = collapseDefault . _optAllowExec
optSaveMetas                 = collapseDefault . _optSaveMetas
optShowIdentitySubstitutions = collapseDefault . _optShowIdentitySubstitutions
optKeepCoveringClauses       = collapseDefault . _optKeepCoveringClauses
optLargeIndices              = collapseDefault . _optLargeIndices
optForcedArgumentRecursion   = collapseDefault . _optForcedArgumentRecursion

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
lensOptNoUniverseCheck f o = f (mapValue not $ _optUniverseCheck o) <&> \ i -> o{ _optUniverseCheck = mapValue not i }

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


-- | Map a function over the long options. Also removes the short options.
--   Will be used to add the plugin name to the plugin options.
mapFlag :: (String -> String) -> OptDescr a -> OptDescr a
mapFlag f (Option _ long arg descr) = Option [] (map f long) arg descr

defaultInteractionOptions :: PragmaOptions
defaultInteractionOptions = defaultPragmaOptions

defaultOptions :: CommandLineOptions
defaultOptions = Options
  { optProgramName      = "agda"
  , optInputFile             = Nothing
  , optIncludePaths          = []
  , optAbsoluteIncludePaths  = []
  , optLibraries             = []
  , optOverrideLibrariesFile = Nothing
  , optDefaultLibs           = True
  , optUseLibs               = True
  , optTraceImports          = 1
  , optTrustedExecutables    = Map.empty
  , optPrintAgdaDataDir      = False
  , optPrintAgdaAppDir       = False
  , optPrintVersion          = Nothing
  , optPrintHelp             = Nothing
  , optInteractive           = False
  , optGHCiInteraction       = False
  , optJSONInteraction       = False
  , optExitOnError           = False
  , optCompileDir            = Nothing
  , optGenerateVimFile       = False
  , optIgnoreInterfaces      = False
  , optIgnoreAllInterfaces   = False
  , optLocalInterfaces       = False
  , optPragmaOptions         = defaultPragmaOptions
  , optOnlyScopeChecking     = False
  , optTransliterate         = False
  , optDiagnosticsColour     = AutoColour
  }

defaultPragmaOptions :: PragmaOptions
defaultPragmaOptions = PragmaOptions
  { _optShowImplicit              = Default
  , _optShowGeneralized           = Default
  , _optShowIrrelevant            = Default
  , _optUseUnicode                = Default -- UnicodeOk
  , _optVerbose                   = Strict.Nothing
  , _optProfiling                 = noProfileOptions
  , _optProp                      = Default
  , _optLevelUniverse             = Default
  , _optTwoLevel                  = Default
  , _optAllowUnsolved             = Default
  , _optAllowIncompleteMatch      = Default
  , _optPositivityCheck           = Default
  , _optTerminationCheck          = Default
  , _optTerminationDepth          = defaultCutOff
  , _optUniverseCheck             = Default
  , _optOmegaInOmega              = Default
  , _optCumulativity              = Default
  , _optSizedTypes                = Default
  , _optGuardedness               = Default
  , _optInjectiveTypeConstructors = Default
  , _optUniversePolymorphism      = Default
  , _optIrrelevantProjections     = Default
  , _optExperimentalIrrelevance   = Default
  , _optWithoutK                  = Default
  , _optCubicalCompatible         = Default
  , _optCopatterns                = Default
  , _optPatternMatching           = Default
  , _optExactSplit                = Default
  , _optHiddenArgumentPuns        = Default
  , _optEta                       = Default
  , _optForcing                   = Default
  , _optProjectionLike            = Default
  , _optErasure                   = Default
  , _optErasedMatches             = Default
  , _optEraseRecordParameters     = Default
  , _optRewriting                 = Default
  , _optCubical                   = Nothing
  , _optGuarded                   = Default
  , _optFirstOrder                = Default
  , _optRequireUniqueMetaSolutions = Default
  , _optPostfixProjections        = Default
  , _optKeepPatternVariables      = Default
  , _optInferAbsurdClauses        = Default
  , _optInstanceSearchDepth       = 500
  , _optBacktrackingInstances      = Default
  , _optQualifiedInstances        = Default
  , _optInversionMaxDepth         = 50
  , _optSafe                      = Default
  , _optDoubleCheck               = Default
  , _optSyntacticEquality         = Strict.Nothing
  , _optWarningMode               = defaultWarningMode
  , _optCompileMain               = Default
  , _optCaching                   = Default
  , _optCountClusters             = Default
  , _optAutoInline                = Default
  , _optPrintPatternSynonyms      = Default
  , _optFastReduce                = Default
  , _optCallByName                = Default
  , _optConfluenceCheck           = Nothing
  , _optCohesion                  = Default
  , _optFlatSplit                 = Default
  , _optPolarity                  = Default
  , _optImportSorts               = Default
  , _optLoadPrimitives            = Default
  , _optAllowExec                 = Default
  , _optSaveMetas                 = Default
  , _optShowIdentitySubstitutions = Default
  , _optKeepCoveringClauses       = Default
  , _optForcedArgumentRecursion   = Default
  , _optLargeIndices              = Default
  }

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
  deriving (Show, Generic)

instance NFData OptionWarning

instance Pretty OptionWarning where
  pretty = \case
    OptionRenamed old new -> hsep
      [ "Option", option old, "is deprecated, please use", option new, "instead" ]
    WarningProblem err -> pretty (prettyWarningModeError err) <+> "See --help=warning."
    where
    option = text . ("--" ++)

optionWarningName :: OptionWarning -> WarningName
optionWarningName = \case
  OptionRenamed{} -> OptionRenamed_
  WarningProblem{} -> WarningProblem_

-- | Checks that the given options are consistent.
--   Also makes adjustments (e.g. when one option implies another).

checkOpts :: MonadError OptionError m => CommandLineOptions -> m CommandLineOptions
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

checkPragmaOptions :: MonadError OptionError m => PragmaOptions -> m PragmaOptions
checkPragmaOptions opts = do

  -- Check for errors in pragma options.

  when ((optEraseRecordParameters `butNot` optErasure) opts) $
    throwError
      "The option --erase-record-parameters requires the use of --erasure"

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
  [ "--cubical-compatible and --with-K" | optCubicalCompatible opts, not (optWithoutK opts) ] ++
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

-- | Infective or coinfective?

data InfectiveCoinfective
  = Infective
  | Coinfective
    deriving (Eq, Show, Generic)

instance NFData InfectiveCoinfective

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
-- Note that @--cubical@ and @--erased-cubical@ are \"jointly
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
  , infectiveOption (isJust . optCubical)     "--cubical/--erased-cubical"
  , infectiveOption optGuarded                "--guarded"
  , infectiveOption optProp                   "--prop"
  , infectiveOption optTwoLevel               "--two-level"
  , infectiveOption optRewriting              "--rewriting"
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
    (coinfectiveOption optCubicalCompatible "--cubical-compatible")
      { icOptionOK = \current imported ->
        -- One must use --cubical-compatible in the imported module if
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

inputFlag :: FilePath -> Flag CommandLineOptions
inputFlag f o =
    case optInputFile o of
        Nothing  -> return $ o { optInputFile = Just f }
        Just _   -> throwError "only one input file allowed"

printAgdaDataDirFlag :: Flag CommandLineOptions
printAgdaDataDirFlag o = return $ o { optPrintAgdaDataDir = True }

printAgdaAppDirFlag :: Flag CommandLineOptions
printAgdaAppDirFlag o = return $ o { optPrintAgdaAppDir = True }

versionFlag :: Flag CommandLineOptions
versionFlag o = return $ o { optPrintVersion = Just PrintAgdaVersion }

numericVersionFlag :: Flag CommandLineOptions
numericVersionFlag o = return $ o { optPrintVersion = Just PrintAgdaNumericVersion }

helpFlag :: Maybe String -> Flag CommandLineOptions
helpFlag Nothing    o = return $ o { optPrintHelp = Just GeneralHelp }
helpFlag (Just str) o = case string2HelpTopic str of
  Just hpt -> return $ o { optPrintHelp = Just (HelpFor hpt) }
  Nothing -> throwError $ "unknown help topic " ++ str ++ " (available: " ++
                           intercalate ", " (map fst allHelpTopics) ++ ")"

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

localInterfacesFlag :: Flag CommandLineOptions
localInterfacesFlag o = return $ o { optLocalInterfaces = True }

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
  , _optTwoLevel                = setDefault True  $ _optTwoLevel o
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
libraryFlag s o = return $ o { optLibraries = optLibraries o ++ [s] }

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

standardOptions :: [OptDescr (Flag CommandLineOptions)]
standardOptions =
    [ Option ['V']  ["version"] (NoArg versionFlag)
                    ("print version information and exit")

    , Option []     ["numeric-version"] (NoArg numericVersionFlag)
                    ("print version number and exit")

    , Option ['?']  ["help"]    (OptArg helpFlag "TOPIC") $ concat
                    [ "print help and exit; available "
                    , String.pluralS allHelpTopics "TOPIC"
                    , ": "
                    , intercalate ", " $ map fst allHelpTopics
                    ]

    , Option []     ["print-agda-dir"] (NoArg printAgdaDataDirFlag)
                    ("print the Agda data directory exit")

    , Option []     ["print-agda-app-dir"] (NoArg printAgdaAppDirFlag)
                    ("print $AGDA_DIR and exit")

    , Option []     ["print-agda-data-dir"] (NoArg printAgdaDataDirFlag)
                    ("print the Agda data directory exit")


    , Option ['I']  ["interactive"] (NoArg interactiveFlag)
                    "start in interactive mode"
    , Option []     ["interaction"] (NoArg ghciInteractionFlag)
                    "for use with the Emacs mode"
    , Option []     ["interaction-json"] (NoArg jsonInteractionFlag)
                    "for use with other editors such as Atom"
    , Option []     ["interaction-exit-on-error"]
                    (NoArg interactionExitFlag)
                    "exit if a type error is encountered"

    , Option []     ["compile-dir"] (ReqArg compileDirFlag "DIR")
                    ("directory for compiler output (default: the project root)")

    , Option []     ["trace-imports"] (OptArg traceImportsFlag "LEVEL")
                    ("print information about accessed modules during type-checking (where LEVEL=0|1|2|3, default: 2)")

    , Option []     ["vim"] (NoArg vimFlag)
                    "generate Vim highlighting files"
    , Option []     ["ignore-interfaces"] (NoArg ignoreInterfacesFlag)
                    "ignore interface files (re-type check everything)"
    , Option []     ["local-interfaces"] (NoArg localInterfacesFlag)
                    "put new interface files next to the Agda files they correspond to"
    , Option ['i']  ["include-path"] (ReqArg includeFlag "DIR")
                    "look for imports in DIR"
    , Option ['l']  ["library"] (ReqArg libraryFlag "LIB")
                    "use library LIB"
    , Option []     ["library-file"] (ReqArg overrideLibrariesFileFlag "FILE")
                    "use FILE instead of the standard libraries file"
    , Option []     ["no-libraries"] (NoArg noLibsFlag)
                    "don't use any library files"
    , Option []     ["no-default-libraries"] (NoArg noDefaultLibsFlag)
                    "don't use default libraries"
    , Option []     ["only-scope-checking"] (NoArg onlyScopeCheckingFlag)
                    "only scope-check the top-level module, do not type-check it"
    , Option []     ["transliterate"] (NoArg transliterateFlag)
                    "transliterate unsupported code points when printing to stdout/stderr"
    , Option []     ["colour", "color"] (OptArg diagnosticsColour "always|auto|never")
                    ("whether or not to colour diagnostics output. The default is auto.")
    ] ++ map (fmap lensPragmaOptions) pragmaOptions

-- | Defined locally here since module ''Agda.Interaction.Options.Lenses''
--   has cyclic dependency.
lensPragmaOptions :: Lens' CommandLineOptions PragmaOptions
lensPragmaOptions f st = f (optPragmaOptions st) <&> \ opts -> st { optPragmaOptions = opts }

-- | Command line options of previous versions of Agda.
--   Should not be listed in the usage info, put parsed by GetOpt for good error messaging.
deadStandardOptions :: [OptDescr (Flag CommandLineOptions)]
deadStandardOptions =
    [ removedOption "sharing"    msgSharing
    , removedOption "no-sharing" msgSharing
    , Option []     ["ignore-all-interfaces"] (NoArg ignoreAllInterfacesFlag) -- not deprecated! Just hidden
                    "ignore all interface files (re-type check everything, including builtin files)"
      -- https://github.com/agda/agda/issues/3522#issuecomment-461010898
      -- The option is "developer only", so it is hidden.
      -- However, it is documented in the user manual.
    ] ++ map (fmap lensPragmaOptions) deadPragmaOptions
  where
    msgSharing = "(in favor of the Agda abstract machine)"

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


pragmaOptions :: [OptDescr (Flag PragmaOptions)]
pragmaOptions = concat
  [ pragmaFlag      "show-implicit" lensOptShowImplicit
                    "show implicit arguments when printing" ""
                    Nothing
  , pragmaFlag      "show-irrelevant" lensOptShowIrrelevant
                    "show irrelevant arguments when printing" ""
                    Nothing
  , pragmaFlag      "show-identity-substitutions" lensOptShowIdentitySubstitutions
                    "show all arguments of metavariables when printing terms" ""
                    Nothing
  , pragmaFlag'     "unicode" lensOptUseUnicode unicodeOrAsciiEffect
                    "use unicode characters when printing terms" ""
                    Nothing
  , [ Option ['v']  ["verbose"] (ReqArg verboseFlag "N")
                    "set verbosity level to N. Only has an effect if Agda was built with the \"debug\" flag."
    , Option []     ["profile"] (ReqArg profileFlag "TYPE")
                    ("turn on profiling for TYPE (where TYPE=" ++ intercalate "|" validProfileOptionStrings ++ ")")
    ]
  , pragmaFlag      "allow-unsolved-metas" lensOptAllowUnsolved
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
                    "allow termination checker to count decrease/increase upto N (default N=1)"
    ]
  , pragmaFlag      "type-in-type" lensOptNoUniverseCheck
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
  , pragmaFlag      "sized-types" lensOptSizedTypes
                    "enable sized types" "(inconsistent with --guardedness)"
                    $ Just "disable sized types"
  , pragmaFlag      "cohesion" lensOptCohesion
                    "enable the cohesion modalities" "(in particular @flat)"
                    Nothing
  , pragmaFlag      "flat-split" lensOptFlatSplit
                    "allow splitting on `(@flat x : A)' arguments" "(implies --cohesion)"
                    Nothing
  , pragmaFlag      "polarity" lensOptPolarity
                    "enable the polarity modalities (@++, @mixed, etc.) and their integration in the positivity checker" ""
                    Nothing
  , pragmaFlag      "guardedness" lensOptGuardedness
                    "enable constructor-based guarded corecursion" "(inconsistent with --sized-types)"
                    $ Just "disable constructor-based guarded corecursion"
  , pragmaFlag      "injective-type-constructors" lensOptInjectiveTypeConstructors
                    "enable injective type constructors" "(makes Agda anti-classical and possibly inconsistent)"
                    $ Just "disable injective type constructors"
  , pragmaFlag      "universe-polymorphism" lensOptUniversePolymorphism
                    "enable universe polymorphism" ""
                    $ Just "disable universe polymorphism"
  , pragmaFlag      "irrelevant-projections" lensOptIrrelevantProjections
                    "enable projection of irrelevant record fields and similar irrelevant definitions" "(inconsistent)"
                    $ Just "disable projection of irrelevant record fields and similar irrelevant definitions"
  , pragmaFlag      "experimental-irrelevance" lensOptExperimentalIrrelevance
                    "enable potentially unsound irrelevance features" "(irrelevant levels, irrelevant data matching)"
                    Nothing
  , [ Option []     ["with-K"] (NoArg withKFlag)
                    "enable the K rule in pattern matching (default)"
    , Option []     ["cubical-compatible"] (NoArg cubicalCompatibleFlag)
                    "turn on generation of auxiliary code required for --cubical, implies --without-K"
    , Option []     ["without-K"] (NoArg withoutKFlag)
                    "turn on checks to make code compatible with HoTT (e.g. disabling the K rule). Implies --no-flat-split."
    ]
  , pragmaFlag      "copatterns" lensOptCopatterns
                    "enable definitions by copattern matching" ""
                    $ Just "disable definitions by copattern matching"
  , pragmaFlag      "pattern-matching" lensOptPatternMatching
                    "enable pattern matching" ""
                    $ Just "disable pattern matching completely"
  , [ Option []     ["exact-split"] (NoArg $ exactSplitFlag True)
                    "require all clauses in a definition to hold as definitional equalities (unless marked CATCHALL)"
    , Option []     ["no-exact-split"] (NoArg $ exactSplitFlag False)
                    "do not require all clauses in a definition to hold as definitional equalities (default)"
    ]
  , pragmaFlag      "hidden-argument-puns" lensOptHiddenArgumentPuns
                    "interpret the patterns {x} and {{x}} as puns" ""
                    Nothing
  , pragmaFlag      "eta-equality" lensOptEta
                    "default records to eta-equality" ""
                    $ Just "default records to no-eta-equality"
  , pragmaFlag      "forcing" lensOptForcing
                    "enable the forcing analysis for data constructors" "(optimisation)"
                    $ Just "disable the forcing analysis"
  , pragmaFlag      "projection-like" lensOptProjectionLike
                    "enable the analysis whether function signatures liken those of projections" "(optimisation)"
                    $ Just "disable the projection-like analysis"
  , pragmaFlag      "erasure" lensOptErasure
                    "enable erasure" ""
                    Nothing
  , pragmaFlag      "erased-matches" lensOptErasedMatches
                    "allow matching in erased positions for single-constructor types" "(implies --erasure if supplied explicitly)"
                    Nothing
  , pragmaFlag      "erase-record-parameters" lensOptEraseRecordParameters
                    "mark all parameters of record modules as erased" "(implies --erasure)"
                    Nothing
  , pragmaFlag      "rewriting" lensOptRewriting
                    "enable declaration and use of REWRITE rules" ""
                    $ Just "disable declaration and use of REWRITE rules"
  , [ Option []     ["local-confluence-check"] (NoArg $ confluenceCheckFlag LocalConfluenceCheck)
                    "enable checking of local confluence of REWRITE rules"
    , Option []     ["confluence-check"] (NoArg $ confluenceCheckFlag GlobalConfluenceCheck)
                    "enable global confluence checking of REWRITE rules (more restrictive than --local-confluence-check)"
    , Option []     ["no-confluence-check"] (NoArg noConfluenceCheckFlag)
                    "disable confluence checking of REWRITE rules (default)"
    , Option []     ["cubical"] (NoArg $ cubicalFlag CFull)
                    "enable cubical features (e.g. overloads lambdas for paths), implies --cubical-compatible"
    , Option []     ["erased-cubical"] (NoArg $ cubicalFlag CErased)
                    "enable cubical features (some only in erased settings), implies --cubical-compatible"
    ]
  , pragmaFlag      "guarded" lensOptGuarded
                    "enable @lock/@tick attributes" ""
                    $ Just "disable @lock/@tick attributes"
  , lossyUnificationOption
  , requireUniqueMetaSolutionsOptions
  , pragmaFlag      "postfix-projections" lensOptPostfixProjections
                    "prefer postfix projection notation" ""
                    $ Just "prefer prefix projection notation"
  , pragmaFlag      "keep-pattern-variables" lensOptKeepPatternVariables
                    "don't replace variables with dot patterns during case splitting" ""
                    $ Just "replace variables with dot patterns during case splitting"
  , pragmaFlag      "infer-absurd-clauses" lensOptInferAbsurdClauses
                    "eliminate absurd clauses in case splitting and coverage checking" ""
                    $ Just "do not automatically eliminate absurd clauses in case splitting and coverage checking (can speed up type-checking)"
  , [ Option []     ["instance-search-depth"] (ReqArg instanceDepthFlag "N")
                    "set instance search depth to N (default: 500)"
    ]
  , backtrackingInstancesOption
  , pragmaFlag      "qualified-instances" lensOptQualifiedInstances
                    "use instances with qualified names" ""
                    Nothing
  , [ Option []     ["inversion-max-depth"] (ReqArg inversionMaxDepthFlag "N")
                    "set maximum depth for pattern match inversion to N (default: 50)"
    , Option []     ["safe"] (NoArg safeFlag)
                    "disable postulates, unsafe OPTION pragmas and primEraseEquality, implies --no-sized-types"
    ]
  , pragmaFlag      "double-check" lensOptDoubleCheck
                    "enable double-checking of all terms using the internal typechecker" ""
                    $ Just "disable double-checking of terms"
  , [ Option []     ["no-syntactic-equality"] (NoArg $ syntacticEqualityFlag (Just "0"))
                    "disable the syntactic equality shortcut in the conversion checker"
    , Option []     ["syntactic-equality"] (OptArg syntacticEqualityFlag "FUEL")
                    "give the syntactic equality shortcut FUEL units of fuel (default: unlimited)"
    , Option ['W']  ["warning"] (ReqArg warningModeFlag "FLAG")
                    ("set warning flags. See --help=warning.")
    ]
  , pragmaFlag      "main" lensOptCompileMain
                    "treat the requested module as the main module of a program when compiling" ""
                    Nothing
  , pragmaFlag      "caching" lensOptCaching
                    "enable caching of typechecking" ""
                    $ Just "disable caching of typechecking"
  , pragmaFlag      "count-clusters" lensOptCountClusters
                    "count extended grapheme clusters when generating LaTeX"
                    ("(note that this flag " ++
#ifdef COUNT_CLUSTERS
                      "is not enabled in all builds"
#else
                      "has not been enabled in this build"
#endif
                      ++ " of Agda)")
                    Nothing
  , pragmaFlag      "auto-inline" lensOptAutoInline
                    "enable automatic compile-time inlining" ""
                    $ Just "disable automatic compile-time inlining, only definitions marked INLINE will be inlined"
  , pragmaFlag      "print-pattern-synonyms" lensOptPrintPatternSynonyms
                    "keep pattern synonyms when printing terms" ""
                    $ Just "expand pattern synonyms when printing terms"
  , pragmaFlag      "fast-reduce" lensOptFastReduce
                    "enable reduction using the Agda Abstract Machine" ""
                    $ Just "disable reduction using the Agda Abstract Machine"
  , pragmaFlag      "call-by-name" lensOptCallByName
                    "use call-by-name evaluation instead of call-by-need" ""
                    $ Just "use call-by-need evaluation"

  , pragmaFlag      "import-sorts" lensOptImportSorts
                    "implicitly import Agda.Primitive using (Set; Prop) at the start of each top-level module" ""
                    $ Just "disable the implicit import of Agda.Primitive using (Set; Prop) at the start of each top-level module"
  , pragmaFlag      "load-primitives" lensOptLoadPrimitives
                    "load primitives modules" ""
                    $ Just "disable loading of primitive modules completely (implies --no-import-sorts)"
  , pragmaFlag      "allow-exec" lensOptAllowExec
                    "allow system calls to trusted executables with primExec" ""
                    Nothing
  , pragmaFlag      "save-metas" lensOptSaveMetas
                    "save meta-variables" ""
                    Nothing
  , pragmaFlag      "keep-covering-clauses" lensOptKeepCoveringClauses
                    "do not discard covering clauses" "(required for some external backends)"
                    $ Just "discard covering clauses"
  , pragmaFlag      "large-indices" lensOptLargeIndices
                    "allow constructors with large indices" ""
                    $ Just "always check that constructor arguments live in universes compatible with that of the datatype"
  , pragmaFlag      "forced-argument-recursion" lensOptForcedArgumentRecursion
                    "allow recursion on forced constructor arguments" ""
                    Nothing
  ]

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

-- | Simple interface for System.Console.GetOpt
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

-- | The usage info message. The argument is the program name (probably
--   agda).
usage :: [OptDescr ()] -> String -> Help -> String
usage options progName GeneralHelp = usageInfo (header progName) options
    where
        header progName = unlines [ "Agda version " ++ version, ""
                                  , "Usage: " ++ progName ++ " [OPTIONS...] [FILE]" ]

usage options progName (HelpFor topic) = helpTopicUsage topic

-- | Removes RTS options from a list of options.

stripRTS :: [String] -> [String]
stripRTS [] = []
stripRTS ("--RTS" : argv) = argv
stripRTS (arg : argv)
  | is "+RTS" arg = stripRTS $ drop 1 $ dropWhile (not . is "-RTS") argv
  | otherwise     = arg : stripRTS argv
  where
    is x arg = [x] == take 1 (words arg)
