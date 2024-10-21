{-# LANGUAGE DataKinds #-}

{-# OPTIONS_GHC -Wunused-imports #-}

-- | A module defining the types exported by "Agda.Interaction.Options" for use in the rest of the codebase.
--
-- This is a boot module to avoid cyclic module dependencies.
-- Only put types and trivial instances here.

module Agda.Interaction.Options.Types where

import           Control.DeepSeq                   ( NFData )
import           Data.Functor                      ( (<&>) )
import           Data.Map                          ( Map )
import           GHC.Generics                      ( Generic )

import           Agda.Syntax.Common                ( Cubical )
import           Agda.Syntax.Concrete.Glyph        ( UnicodeOrAscii )
import           Agda.Interaction.Library          ( ExeName, LibName )
import           Agda.Interaction.Options.Help     ( Help )
import           Agda.Interaction.Options.Warnings ( WarningMode )
import           Agda.Termination.CutOff           ( CutOff )

import           Agda.Utils.FileName               ( AbsolutePath )
import           Agda.Utils.Lens                   ( Lens', (^.), over )
import           Agda.Utils.List1                  ( String1 )
import qualified Agda.Utils.Maybe.Strict           as Strict
import           Agda.Utils.ProfileOptions         ( ProfileOptions )
import           Agda.Utils.Trie                   ( Trie )
import           Agda.Utils.WithDefault            ( WithDefault, WithDefault' )

---------------------------------------------------------------------------
-- * Option records

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
      -- ^ Should the conversion checker use the syntactic equality shortcut?
      -- 'Nothing' means that it should.
      -- @'Just' n@, for a non-negative number @n@, means that syntactic equality
      -- checking gets @n@ units of fuel.
      -- If the fuel becomes zero, then syntactic equality checking is turned off.
      -- The fuel counter is decreased in the failure continuation of
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

---------------------------------------------------------------------------
-- * Auxiliary structures (by default in alphabetic order)

data ConfluenceCheck
  = LocalConfluenceCheck
  | GlobalConfluenceCheck
  deriving (Show, Eq, Generic)

data DiagnosticsColours
  = AlwaysColour
  | NeverColour
  | AutoColour
  deriving (Show, Generic)

-- | Infective or coinfective?
data InfectiveCoinfective
  = Infective
  | Coinfective
  deriving (Eq, Show, Generic)

-- | Options @--version@ and @--numeric-version@ (last wins).
data PrintAgdaVersion
  = PrintAgdaVersion
      -- ^ Print Agda version information and exit.
  | PrintAgdaNumericVersion
      -- ^ Print Agda version number and exit.
  deriving (Show, Generic)

type VerboseKey     = String
type VerboseKeyItem = String1
type VerboseLevel   = Int

-- | 'Strict.Nothing' is used if no verbosity options have been given,
-- thus making it possible to handle the default case relatively
-- quickly. Note that 'Strict.Nothing' corresponds to a trie with
-- verbosity level 1 for the empty path.
type Verbosity = Strict.Maybe (Trie VerboseKeyItem VerboseLevel)

---------------------------------------------------------------------------
-- * Lenses

class LensPragmaOptions a where
  getPragmaOptions  :: a -> PragmaOptions
  setPragmaOptions  :: PragmaOptions -> a -> a
  mapPragmaOptions  :: (PragmaOptions -> PragmaOptions) -> a -> a
  lensPragmaOptions :: Lens' a PragmaOptions

  {-# MINIMAL lensPragmaOptions #-}
  getPragmaOptions = (^. lensPragmaOptions)
  setPragmaOptions = mapPragmaOptions . const
  mapPragmaOptions = over lensPragmaOptions

instance LensPragmaOptions CommandLineOptions where
  lensPragmaOptions f st = f (optPragmaOptions st) <&> \ opts -> st { optPragmaOptions = opts }

---------------------------------------------------------------------------
-- NFData instances

instance NFData CommandLineOptions
instance NFData PragmaOptions

instance NFData ConfluenceCheck
instance NFData DiagnosticsColours
instance NFData InfectiveCoinfective
instance NFData PrintAgdaVersion
