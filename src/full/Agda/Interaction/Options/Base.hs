{-# LANGUAGE CPP       #-}
{-# LANGUAGE DataKinds #-}

module Agda.Interaction.Options.Base
    ( CommandLineOptions(..)
    , PragmaOptions(..)
    , OptionsPragma
    , OptionWarning(..), optionWarningName
    , Flag, OptM, runOptM, OptDescr(..), ArgDescr(..)
    , Verbosity, VerboseKey, VerboseLevel
    , WarningMode(..)
    , ConfluenceCheck(..)
    , UnicodeOrAscii(..)
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
    , safeFlag
    , mapFlag
    , usage
    -- Reused by PandocAgda
    , inputFlag
    , standardOptions, deadStandardOptions
    , getOptSimple
    ) where

import Prelude hiding ( null )

import Control.DeepSeq
import Control.Monad ( when, void )
import Control.Monad.Except ( ExceptT, MonadError(throwError), runExceptT )
import Control.Monad.Writer ( Writer, runWriter, MonadWriter(..) )

import qualified System.IO.Unsafe as UNSAFE (unsafePerformIO)
import Data.Maybe
import Data.Map                 ( Map )
import qualified Data.Map as Map
import Data.List                ( intercalate )
import qualified Data.Set as Set

import GHC.Generics (Generic)

import System.Console.GetOpt    ( getOpt', usageInfo, ArgOrder(ReturnInOrder)
                                , OptDescr(..), ArgDescr(..)
                                )
import Text.EditDistance
import Text.Read                ( readMaybe )

import Agda.Termination.CutOff  ( CutOff(..), defaultCutOff )

import Agda.Interaction.Library ( ExeName, LibName )
import Agda.Interaction.Options.Help
  ( Help(HelpFor, GeneralHelp)
  , string2HelpTopic
  , allHelpTopics
  , helpTopicUsage
  )
import Agda.Interaction.Options.Warnings
import Agda.Syntax.Concrete.Glyph ( unsafeSetUnicodeOrAscii, UnicodeOrAscii(..) )
import Agda.Syntax.Common (Cubical(..))
import Agda.Syntax.TopLevelModuleName (TopLevelModuleName)

import Agda.Utils.FileName      ( AbsolutePath )
import Agda.Utils.Functor       ( (<&>) )
import Agda.Utils.Lens          ( Lens', over )
import Agda.Utils.List          ( groupOn, initLast1 )
import Agda.Utils.List1         ( String1, toList )
import qualified Agda.Utils.List1        as List1
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad         ( tell1 )
import Agda.Utils.Null
import Agda.Utils.Pretty
import Agda.Utils.ProfileOptions
import Agda.Utils.Trie          ( Trie )
import qualified Agda.Utils.Trie as Trie
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
  -- ^ Use this (if Just) instead of .agda/libraries
  , optDefaultLibs           :: Bool
  -- ^ Use ~/.agda/defaults
  , optUseLibs               :: Bool
  -- ^ look for .agda-lib files
  , optTraceImports          :: Integer
  -- ^ Configure notifications about imported modules
  , optTrustedExecutables    :: Map ExeName FilePath
  -- ^ Map names of trusted executables to absolute paths
  , optPrintAgdaDir          :: Bool
  , optPrintVersion          :: Bool
  , optPrintHelp             :: Maybe Help
  , optInteractive           :: Bool
      -- ^ Agda REPL (-I).
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
    -- ^ Should the top-level module only be scope-checked, and not
    --   type-checked?
  , optTransliterate         :: Bool
    -- ^ Should code points that are not supported by the locale be transliterated?
  }
  deriving (Show, Generic)

instance NFData CommandLineOptions

-- | Options which can be set in a pragma.

data PragmaOptions = PragmaOptions
  { optShowImplicit              :: Bool
  , optShowIrrelevant            :: Bool
  , optUseUnicode                :: UnicodeOrAscii
  , optVerbose                   :: !Verbosity
  , optProfiling                 :: ProfileOptions
  , optProp                      :: Bool
  , optTwoLevel                  :: WithDefault 'False
  , optAllowUnsolved             :: Bool
  , optAllowIncompleteMatch      :: Bool
  , optDisablePositivity         :: Bool
  , optTerminationCheck          :: Bool
  , optTerminationDepth          :: CutOff
    -- ^ Cut off structural order comparison at some depth in termination checker?
  , optUniverseCheck             :: Bool
  , optOmegaInOmega              :: Bool
  , optCumulativity              :: Bool
  , optSizedTypes                :: WithDefault 'False
  , optGuardedness               :: WithDefault 'False
  , optInjectiveTypeConstructors :: Bool
  , optUniversePolymorphism      :: Bool
  , optIrrelevantProjections     :: Bool
  , optExperimentalIrrelevance   :: Bool  -- ^ irrelevant levels, irrelevant data matching
  , optWithoutK                  :: WithDefault 'False
  , optCubicalCompatible         :: WithDefault 'False
  , optCopatterns                :: Bool  -- ^ Allow definitions by copattern matching?
  , optPatternMatching           :: Bool  -- ^ Is pattern matching allowed in the current file?
  , optExactSplit                :: Bool
  , optEta                       :: Bool
  , optForcing                   :: Bool  -- ^ Perform the forcing analysis on data constructors?
  , optProjectionLike            :: Bool  -- ^ Perform the projection-likeness analysis on functions?
  , optEraseRecordParameters     :: Bool  -- ^ Mark parameters of record modules as erased?
  , optRewriting                 :: Bool  -- ^ Can rewrite rules be added and used?
  , optCubical                   :: Maybe Cubical
  , optGuarded                   :: Bool
  , optFirstOrder                :: Bool  -- ^ Should we speculatively unify function applications as if they were injective?
  , optPostfixProjections        :: Bool
      -- ^ Should system generated projections 'ProjSystem' be printed
      --   postfix (True) or prefix (False).
  , optKeepPatternVariables      :: Bool
      -- ^ Should case splitting replace variables with dot patterns
      --   (False) or keep them as variables (True).
  , optInstanceSearchDepth       :: Int
  , optOverlappingInstances      :: Bool
  , optQualifiedInstances        :: Bool  -- ^ Should instance search consider instances with qualified names?
  , optInversionMaxDepth         :: Int
  , optSafe                      :: Bool
  , optDoubleCheck               :: Bool
  , optSyntacticEquality         :: !(Strict.Maybe Int)
    -- ^ Should the conversion checker use the syntactic equality
    -- shortcut? 'Nothing' means that it should. @'Just' n@, for a
    -- non-negative number @n@, means that syntactic equality checking
    -- gets @n@ units of fuel. If the fuel becomes zero, then
    -- syntactic equality checking is turned off. The fuel counter is
    -- decreased in the failure continuation of
    -- 'Agda.TypeChecking.SyntacticEquality.checkSyntacticEquality'.
  , optWarningMode               :: WarningMode
  , optCompileNoMain             :: Bool
  , optCaching                   :: Bool
  , optCountClusters             :: Bool
    -- ^ Count extended grapheme clusters rather than code points when
    -- generating LaTeX.
  , optAutoInline                :: Bool
    -- ^ Automatic compile-time inlining for simple definitions (unless marked
    --   NOINLINE).
  , optPrintPatternSynonyms      :: Bool
  , optFastReduce                :: Bool
    -- ^ Use the Agda abstract machine (fastReduce)?
  , optCallByName                :: Bool
    -- ^ Use call-by-name instead of call-by-need
  , optConfluenceCheck           :: Maybe ConfluenceCheck
    -- ^ Check confluence of rewrite rules?
  , optCohesion                  :: Bool
     -- ^ Are the cohesion modalities available?
  , optFlatSplit                 :: WithDefault 'False
     -- ^ Can we split on a (@flat x : A) argument?
  , optImportSorts               :: Bool
     -- ^ Should every top-level module start with an implicit statement
     --   @open import Agda.Primitive using (Set; Prop)@?
  , optLoadPrimitives            :: Bool
    -- ^ Should we load the primitive modules at all? This is a stronger
    -- form of 'optImportSorts'.
  , optAllowExec                 :: Bool
  , optSaveMetas                 :: WithDefault 'False
    -- ^ Save meta-variables.
  , optShowIdentitySubstitutions :: Bool
    -- ^ Show identity substitutions when pretty-printing terms
    --   (i.e. always show all arguments of a metavariable)
  , optKeepCoveringClauses       :: Bool
    -- ^ Do not discard clauses constructed by the coverage checker
    --   (needed for some external backends)
  }
  deriving (Show, Eq, Generic)

instance NFData PragmaOptions

data ConfluenceCheck
  = LocalConfluenceCheck
  | GlobalConfluenceCheck
  deriving (Show, Eq, Generic)

instance NFData ConfluenceCheck

-- | The options from an @OPTIONS@ pragma.
--
-- In the future it might be nice to switch to a more structured
-- representation. Note that, currently, there is not a one-to-one
-- correspondence between list elements and options.
type OptionsPragma = [String]

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
  , optPrintAgdaDir          = False
  , optPrintVersion          = False
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
  }

defaultPragmaOptions :: PragmaOptions
defaultPragmaOptions = PragmaOptions
  { optShowImplicit              = False
  , optShowIrrelevant            = False
  , optUseUnicode                = UnicodeOk
  , optVerbose                   = Strict.Nothing
  , optProfiling                 = noProfileOptions
  , optProp                      = False
  , optTwoLevel                  = Default
  , optExperimentalIrrelevance   = False
  , optIrrelevantProjections     = False -- off by default in > 2.5.4, see issue #2170
  , optAllowUnsolved             = False
  , optAllowIncompleteMatch      = False
  , optDisablePositivity         = False
  , optTerminationCheck          = True
  , optTerminationDepth          = defaultCutOff
  , optUniverseCheck             = True
  , optOmegaInOmega              = False
  , optCumulativity              = False
  , optSizedTypes                = Default
  , optGuardedness               = Default
  , optInjectiveTypeConstructors = False
  , optUniversePolymorphism      = True
  , optWithoutK                  = Default
  , optCubicalCompatible         = Default
  , optCopatterns                = True
  , optPatternMatching           = True
  , optExactSplit                = False
  , optEta                       = True
  , optForcing                   = True
  , optProjectionLike            = True
  , optEraseRecordParameters     = False
  , optRewriting                 = False
  , optCubical                   = Nothing
  , optGuarded                   = False
  , optFirstOrder                = False
  , optPostfixProjections        = False
  , optKeepPatternVariables      = False
  , optInstanceSearchDepth       = 500
  , optOverlappingInstances      = False
  , optQualifiedInstances        = True
  , optInversionMaxDepth         = 50
  , optSafe                      = False
  , optDoubleCheck               = False
  , optSyntacticEquality         = Strict.Nothing
  , optWarningMode               = defaultWarningMode
  , optCompileNoMain             = False
  , optCaching                   = True
  , optCountClusters             = False
  , optAutoInline                = False
  , optPrintPatternSynonyms      = True
  , optFastReduce                = True
  , optCallByName                = False
  , optConfluenceCheck           = Nothing
  , optCohesion                  = False
  , optFlatSplit                 = Default
  , optImportSorts               = True
  , optAllowExec                 = False
  , optSaveMetas                 = Default
  , optShowIdentitySubstitutions = False
  , optLoadPrimitives            = True
  , optKeepCoveringClauses       = False
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
  deriving (Show, Generic)

instance NFData OptionWarning

instance Pretty OptionWarning where
  pretty = \case
    OptionRenamed old new -> hsep
      [ "Option", name old, "is deprecated, please use", name new, "instead" ]
    where
    name = text . ("--" ++)

optionWarningName :: OptionWarning -> WarningName
optionWarningName = \case
  OptionRenamed{} -> OptionRenamed_

-- | Checks that the given options are consistent.

checkOpts :: MonadError OptionError m => CommandLineOptions -> m ()
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

-- | Check for unsafe pragmas. Gives a list of used unsafe flags.

unsafePragmaOptions :: PragmaOptions -> [String]
unsafePragmaOptions opts =
  [ "--allow-unsolved-metas"                     | optAllowUnsolved opts             ] ++
  [ "--allow-incomplete-matches"                 | optAllowIncompleteMatch opts      ] ++
  [ "--no-positivity-check"                      | optDisablePositivity opts         ] ++
  [ "--no-termination-check"                     | not (optTerminationCheck opts)    ] ++
  [ "--type-in-type"                             | not (optUniverseCheck opts)       ] ++
  [ "--omega-in-omega"                           | optOmegaInOmega opts              ] ++
  [ "--sized-types"                              | collapseDefault (optSizedTypes opts) ] ++
  [ "--injective-type-constructors"              | optInjectiveTypeConstructors opts ] ++
  [ "--irrelevant-projections"                   | optIrrelevantProjections opts     ] ++
  [ "--experimental-irrelevance"                 | optExperimentalIrrelevance opts   ] ++
  [ "--rewriting"                                | optRewriting opts                 ] ++
  [ "--cubical-compatible and --with-K"          | collapseDefault (optCubicalCompatible opts)
                                                 , not (collapseDefault $ optWithoutK opts) ] ++
  [ "--without-K and --flat-split"               | collapseDefault (optWithoutK opts)
                                                 , collapseDefault (optFlatSplit opts) ] ++
  [ "--cumulativity"                             | optCumulativity opts              ] ++
  [ "--allow-exec"                               | optAllowExec opts                 ] ++
  [ "--no-load-primitives"                       | not $ optLoadPrimitives opts      ] ++
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
  blankOut opts = opts
    { optShowImplicit              = False
    , optShowIrrelevant            = False
    , optVerbose                   = empty
    , optProfiling                 = noProfileOptions
    , optPostfixProjections        = False
    , optCompileNoMain             = False
    , optCaching                   = False
    , optCountClusters             = False
    , optPrintPatternSynonyms      = False
    , optShowIdentitySubstitutions = False
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
  [ coinfectiveOption optSafe "--safe"
  , coinfectiveOption (collapseDefault . optWithoutK) "--without-K"
  , cubicalCompatible
  , coinfectiveOption (not . optUniversePolymorphism)
                      "--no-universe-polymorphism"
  , coinfectiveOption (not . optCumulativity) "--no-cumulativity"
  , infectiveOption (isJust . optCubical) "--cubical/--erased-cubical"
  , infectiveOption optGuarded "--guarded"
  , infectiveOption optProp "--prop"
  , infectiveOption (collapseDefault . optTwoLevel) "--two-level"
  , infectiveOption optRewriting "--rewriting"
  , infectiveOption (collapseDefault . optSizedTypes) "--sized-types"
  , infectiveOption (collapseDefault . optGuardedness) "--guardedness"
  , infectiveOption (collapseDefault . optFlatSplit) "--flat-split"
  , infectiveOption optCohesion "--cohesion"
  ]
  where
  cubicalCompatible =
    (coinfectiveOption
       (collapseDefault . optCubicalCompatible)
       "--cubical-compatible")
      { icOptionOK = \current imported ->
        -- One must use --cubical-compatible in the imported module if
        -- it is used in the current module, except if the current
        -- module also uses --with-K and not --safe, and the imported
        -- module uses --with-K.
        if collapseDefault (optCubicalCompatible current)
        then collapseDefault (optCubicalCompatible imported)
               ||
             not (collapseDefault (optWithoutK imported))
               &&
             not (collapseDefault (optWithoutK current))
               &&
             not (optSafe current)
        else True
      }

inputFlag :: FilePath -> Flag CommandLineOptions
inputFlag f o =
    case optInputFile o of
        Nothing  -> return $ o { optInputFile = Just f }
        Just _   -> throwError "only one input file allowed"

printAgdaDirFlag :: Flag CommandLineOptions
printAgdaDirFlag o = return $ o { optPrintAgdaDir = True }

versionFlag :: Flag CommandLineOptions
versionFlag o = return $ o { optPrintVersion = True }

helpFlag :: Maybe String -> Flag CommandLineOptions
helpFlag Nothing    o = return $ o { optPrintHelp = Just GeneralHelp }
helpFlag (Just str) o = case string2HelpTopic str of
  Just hpt -> return $ o { optPrintHelp = Just (HelpFor hpt) }
  Nothing -> throwError $ "unknown help topic " ++ str ++ " (available: " ++
                           intercalate ", " (map fst allHelpTopics) ++ ")"

safeFlag :: Flag PragmaOptions
safeFlag o = do
  let sizedTypes  = optSizedTypes o
  return $ o { optSafe        = True
             , optSizedTypes  = setDefault False sizedTypes
             }

cohesionFlag :: Flag PragmaOptions
cohesionFlag o = return $ o { optCohesion = True }

flatSplitFlag :: Flag PragmaOptions
flatSplitFlag o = return $ o
  { optFlatSplit = Value True
  , optCohesion  = True
  }

doubleCheckFlag :: Bool -> Flag PragmaOptions
doubleCheckFlag b o = return $ o { optDoubleCheck = b }

syntacticEqualityFlag :: Maybe String -> Flag PragmaOptions
syntacticEqualityFlag s o =
  case fuel of
    Left err   -> throwError err
    Right fuel -> return $ o { optSyntacticEquality = fuel }
  where
  fuel = case s of
    Nothing -> Right Strict.Nothing
    Just s  -> case readMaybe s of
      Just n | n >= 0 -> Right (Strict.Just n)
      _               -> Left $ "Not a natural number: " ++ s

cachingFlag :: Bool -> Flag PragmaOptions
cachingFlag b o = return $ o { optCaching = b }

propFlag :: Flag PragmaOptions
propFlag o = return $ o { optProp = True }

noPropFlag :: Flag PragmaOptions
noPropFlag o = return $ o { optProp = False }

twoLevelFlag :: Flag PragmaOptions
twoLevelFlag o = return $ o { optTwoLevel = Value True }

experimentalIrrelevanceFlag :: Flag PragmaOptions
experimentalIrrelevanceFlag o = return $ o { optExperimentalIrrelevance = True }

irrelevantProjectionsFlag :: Flag PragmaOptions
irrelevantProjectionsFlag o = return $ o { optIrrelevantProjections = True }

noIrrelevantProjectionsFlag :: Flag PragmaOptions
noIrrelevantProjectionsFlag o = return $ o { optIrrelevantProjections = False }

ignoreInterfacesFlag :: Flag CommandLineOptions
ignoreInterfacesFlag o = return $ o { optIgnoreInterfaces = True }

ignoreAllInterfacesFlag :: Flag CommandLineOptions
ignoreAllInterfacesFlag o = return $ o { optIgnoreAllInterfaces = True }

localInterfacesFlag :: Flag CommandLineOptions
localInterfacesFlag o = return $ o { optLocalInterfaces = True }

noLoadPrimitivesFlag :: Flag PragmaOptions
noLoadPrimitivesFlag o = return $ o
  { optLoadPrimitives = False
  , optImportSorts = False
  }

allowUnsolvedFlag :: Flag PragmaOptions
allowUnsolvedFlag o = do
  let upd = over warningSet (Set.\\ unsolvedWarnings)
  return $ o { optAllowUnsolved = True
             , optWarningMode   = upd (optWarningMode o)
             }

allowIncompleteMatchFlag :: Flag PragmaOptions
allowIncompleteMatchFlag o = do
  let upd = over warningSet (Set.\\ incompleteMatchWarnings)
  return $ o { optAllowIncompleteMatch = True
             , optWarningMode          = upd (optWarningMode o)
             }

showImplicitFlag :: Flag PragmaOptions
showImplicitFlag o = return $ o { optShowImplicit = True }

showIrrelevantFlag :: Flag PragmaOptions
showIrrelevantFlag o = return $ o { optShowIrrelevant = True }

showIdentitySubstitutionsFlag :: Flag PragmaOptions
showIdentitySubstitutionsFlag o = return $ o { optShowIdentitySubstitutions = True }

traceImportsFlag :: Maybe String -> Flag CommandLineOptions
traceImportsFlag arg o = do
  mode <- case arg of
            Nothing -> return 2
            Just str -> case reads str :: [(Integer, String)] of
                          [(n, "")] -> return n
                          _ -> throwError $ "unknown printing option " ++ str ++ ". Please specify a number."
  return $ o { optTraceImports = mode }

asciiOnlyFlag :: Flag PragmaOptions
asciiOnlyFlag o = return $ UNSAFE.unsafePerformIO $ do
  unsafeSetUnicodeOrAscii AsciiOnly
  return $ o { optUseUnicode = AsciiOnly }

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

countClustersFlag :: Flag PragmaOptions
countClustersFlag o =
#ifdef COUNT_CLUSTERS
  return $ o { optCountClusters = True }
#else
  throwError
    "Cluster counting has not been enabled in this build of Agda."
#endif

noAutoInlineFlag :: Flag PragmaOptions
noAutoInlineFlag o = return $ o { optAutoInline = False }

autoInlineFlag :: Flag PragmaOptions
autoInlineFlag o = return $ o { optAutoInline = True }

noPrintPatSynFlag :: Flag PragmaOptions
noPrintPatSynFlag o = return $ o { optPrintPatternSynonyms = False }

noFastReduceFlag :: Flag PragmaOptions
noFastReduceFlag o = return $ o { optFastReduce = False }

callByNameFlag :: Flag PragmaOptions
callByNameFlag o = return $ o { optCallByName = True }

noPositivityFlag :: Flag PragmaOptions
noPositivityFlag o = do
  let upd = over warningSet (Set.delete NotStrictlyPositive_)
  return $ o { optDisablePositivity = True
             , optWarningMode   = upd (optWarningMode o)
             }

dontTerminationCheckFlag :: Flag PragmaOptions
dontTerminationCheckFlag o = do
  let upd = over warningSet (Set.delete TerminationIssue_)
  return $ o { optTerminationCheck = False
             , optWarningMode   = upd (optWarningMode o)
             }

dontUniverseCheckFlag :: Flag PragmaOptions
dontUniverseCheckFlag o = return $ o { optUniverseCheck = False }

omegaInOmegaFlag :: Flag PragmaOptions
omegaInOmegaFlag o = return $ o { optOmegaInOmega = True }

cumulativityFlag :: Flag PragmaOptions
cumulativityFlag o = return $ o { optCumulativity = True }

noCumulativityFlag :: Flag PragmaOptions
noCumulativityFlag o = return $ o { optCumulativity = False }

--UNUSED Liang-Ting Chen 2019-07-16
--etaFlag :: Flag PragmaOptions
--etaFlag o = return $ o { optEta = True }

noEtaFlag :: Flag PragmaOptions
noEtaFlag o = return $ o { optEta = False }

sizedTypes :: Flag PragmaOptions
sizedTypes o = return $ o { optSizedTypes = Value True }

noSizedTypes :: Flag PragmaOptions
noSizedTypes o = return $ o { optSizedTypes = Value False }

guardedness :: Flag PragmaOptions
guardedness o = return $ o { optGuardedness = Value True }

noGuardedness :: Flag PragmaOptions
noGuardedness o = return $ o { optGuardedness = Value False }

injectiveTypeConstructorFlag :: Flag PragmaOptions
injectiveTypeConstructorFlag o = return $ o { optInjectiveTypeConstructors = True }

universePolymorphismFlag :: Flag PragmaOptions
universePolymorphismFlag o = return $ o { optUniversePolymorphism = True }

noUniversePolymorphismFlag :: Flag PragmaOptions
noUniversePolymorphismFlag  o = return $ o { optUniversePolymorphism = False }

noForcingFlag :: Flag PragmaOptions
noForcingFlag o = return $ o { optForcing = False }

noProjectionLikeFlag :: Flag PragmaOptions
noProjectionLikeFlag o = return $ o { optProjectionLike = False }

withKFlag :: Flag PragmaOptions
withKFlag o = return $ o { optWithoutK = Value False }

withoutKFlag :: Flag PragmaOptions
withoutKFlag o = return $ o
  { optWithoutK = Value True
  , optFlatSplit = setDefault False (optFlatSplit o)
  }

copatternsFlag :: Flag PragmaOptions
copatternsFlag o = return $ o { optCopatterns = True }

noCopatternsFlag :: Flag PragmaOptions
noCopatternsFlag o = return $ o { optCopatterns = False }

noPatternMatchingFlag :: Flag PragmaOptions
noPatternMatchingFlag o = return $ o { optPatternMatching = False }

exactSplitFlag :: Flag PragmaOptions
exactSplitFlag o = do
  let upd = over warningSet (Set.insert CoverageNoExactSplit_)
  return $ o { optExactSplit = True
             , optWarningMode   = upd (optWarningMode o)
             }

noExactSplitFlag :: Flag PragmaOptions
noExactSplitFlag o = do
  let upd = over warningSet (Set.delete CoverageNoExactSplit_)
  return $ o { optExactSplit = False
             , optWarningMode   = upd (optWarningMode o)
             }

rewritingFlag :: Flag PragmaOptions
rewritingFlag o = return $ o { optRewriting = True }

firstOrderFlag :: Flag PragmaOptions
firstOrderFlag o = return $ o { optFirstOrder = True }

cubicalCompatibleFlag :: Flag PragmaOptions
cubicalCompatibleFlag o =
  return $ o { optCubicalCompatible = Value True
             , optWithoutK = setDefault True $ optWithoutK o
             , optFlatSplit = setDefault False (optFlatSplit o)
             }

cubicalFlag
  :: Cubical  -- ^ Which variant of Cubical Agda?
  -> Flag PragmaOptions
cubicalFlag variant o =
  return $ o { optCubical  = Just variant
             , optCubicalCompatible = setDefault True $ optCubicalCompatible o
             , optWithoutK = setDefault True $ optWithoutK o
             , optTwoLevel = setDefault True $ optTwoLevel o
             , optFlatSplit = setDefault False (optFlatSplit o)
             }

guardedFlag :: Flag PragmaOptions
guardedFlag o = do
  return $ o { optGuarded  = True }

postfixProjectionsFlag :: Flag PragmaOptions
postfixProjectionsFlag o = return $ o { optPostfixProjections = True }

keepPatternVariablesFlag :: Flag PragmaOptions
keepPatternVariablesFlag o = return $ o { optKeepPatternVariables = True }

instanceDepthFlag :: String -> Flag PragmaOptions
instanceDepthFlag s o = do
  d <- integerArgument "--instance-search-depth" s
  return $ o { optInstanceSearchDepth = d }

overlappingInstancesFlag :: Flag PragmaOptions
overlappingInstancesFlag o = return $ o { optOverlappingInstances = True }

noOverlappingInstancesFlag :: Flag PragmaOptions
noOverlappingInstancesFlag o = return $ o { optOverlappingInstances = False }

qualifiedInstancesFlag :: Flag PragmaOptions
qualifiedInstancesFlag o = return $ o { optQualifiedInstances = True }

noQualifiedInstancesFlag :: Flag PragmaOptions
noQualifiedInstancesFlag o = return $ o { optQualifiedInstances = False }

inversionMaxDepthFlag :: String -> Flag PragmaOptions
inversionMaxDepthFlag s o = do
  d <- integerArgument "--inversion-max-depth" s
  return $ o { optInversionMaxDepth = d }

interactiveFlag :: Flag CommandLineOptions
interactiveFlag  o = return $ o { optInteractive = True }

compileFlagNoMain :: Flag PragmaOptions
compileFlagNoMain o = return $ o { optCompileNoMain = True }

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
          o { optVerbose =
                Strict.Just $ Trie.insert k n $
                case optVerbose o of
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
  case addProfileOption s (optProfiling o) of
    Left err   -> throwError err
    Right prof -> pure o{ optProfiling = prof }

warningModeFlag :: String -> Flag PragmaOptions
warningModeFlag s o = case warningModeUpdate s of
  Right upd -> return $ o { optWarningMode = upd (optWarningMode o) }
  Left err  -> throwError $ prettyWarningModeError err ++ " See --help=warning."

terminationDepthFlag :: String -> Flag PragmaOptions
terminationDepthFlag s o =
    do k <- maybe usage return $ readMaybe s
       when (k < 1) $ usage -- or: turn termination checking off for 0
       return $ o { optTerminationDepth = CutOff $ k-1 }
    where usage = throwError "argument to termination-depth should be >= 1"

confluenceCheckFlag :: ConfluenceCheck -> Flag PragmaOptions
confluenceCheckFlag f o = return $ o { optConfluenceCheck = Just f }

noConfluenceCheckFlag :: Flag PragmaOptions
noConfluenceCheckFlag o = return $ o { optConfluenceCheck = Nothing }

noImportSorts :: Flag PragmaOptions
noImportSorts o = return $ o { optImportSorts = False }

allowExec :: Flag PragmaOptions
allowExec o = return $ o { optAllowExec = True }

saveMetas :: Bool -> Flag PragmaOptions
saveMetas save o = return $ o { optSaveMetas = Value save }

eraseRecordParametersFlag :: Flag PragmaOptions
eraseRecordParametersFlag o = return $ o { optEraseRecordParameters = True }

noEraseRecordParametersFlag :: Flag PragmaOptions
noEraseRecordParametersFlag o = return $ o { optEraseRecordParameters = False }

integerArgument :: String -> String -> OptM Int
integerArgument flag s = maybe usage return $ readMaybe s
  where
  usage = throwError $ "option '" ++ flag ++ "' requires an integer argument"

keepCoveringClausesFlag :: Flag PragmaOptions
keepCoveringClausesFlag o = return $ o { optKeepCoveringClauses = True }


standardOptions :: [OptDescr (Flag CommandLineOptions)]
standardOptions =
    [ Option ['V']  ["version"] (NoArg versionFlag)
                    ("print version number and exit")

    , Option ['?']  ["help"]    (OptArg helpFlag "TOPIC") $ concat
                    [ "print help and exit; available "
                    , singPlural allHelpTopics "TOPIC" "TOPICs"
                    , ": "
                    , intercalate ", " $ map fst allHelpTopics
                    ]

    , Option []     ["print-agda-dir"] (NoArg printAgdaDirFlag)
                    ("print $AGDA_DIR and exit")

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
                    "put interface files next to the Agda files they correspond to"
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
    ] ++ map (fmap lensPragmaOptions) pragmaOptions

-- | Defined locally here since module ''Agda.Interaction.Options.Lenses''
--   has cyclic dependency.
lensPragmaOptions :: Lens' PragmaOptions CommandLineOptions
lensPragmaOptions f st = f (optPragmaOptions st) <&> \ opts -> st { optPragmaOptions = opts }

-- | Command line options of previous versions of Agda.
--   Should not be listed in the usage info, put parsed by GetOpt for good error messaging.
deadStandardOptions :: [OptDescr (Flag CommandLineOptions)]
deadStandardOptions =
    [ removedOption "sharing"    msgSharing
    , removedOption "no-sharing" msgSharing
    , Option []     ["ignore-all-interfaces"] (NoArg ignoreAllInterfacesFlag) -- not deprecated! Just hidden
                    "ignore all interface files (re-type check everything, including builtin files)"
    ] ++ map (fmap lensPragmaOptions) deadPragmaOptions
  where
    msgSharing = "(in favor of the Agda abstract machine)"

pragmaOptions :: [OptDescr (Flag PragmaOptions)]
pragmaOptions =
    [ Option []     ["show-implicit"] (NoArg showImplicitFlag)
                    "show implicit arguments when printing"
    , Option []     ["show-irrelevant"] (NoArg showIrrelevantFlag)
                    "show irrelevant arguments when printing"
    , Option []     ["show-identity-substitutions"] (NoArg showIdentitySubstitutionsFlag)
                    "show all arguments of metavariables when printing terms"
    , Option []     ["no-unicode"] (NoArg asciiOnlyFlag)
                    "don't use unicode characters when printing terms"
    , Option ['v']  ["verbose"] (ReqArg verboseFlag "N")
                    "set verbosity level to N"
    , Option []     ["profile"] (ReqArg profileFlag "TYPE")
                    ("turn on profiling for TYPE (where TYPE=" ++ intercalate "|" validProfileOptionStrings ++ ")")
    , Option []     ["allow-unsolved-metas"] (NoArg allowUnsolvedFlag)
                    "succeed and create interface file regardless of unsolved meta variables"
    , Option []     ["allow-incomplete-matches"] (NoArg allowIncompleteMatchFlag)
                    "succeed and create interface file regardless of incomplete pattern matches"
    , Option []     ["no-positivity-check"] (NoArg noPositivityFlag)
                    "do not warn about not strictly positive data types"
    , Option []     ["no-termination-check"] (NoArg dontTerminationCheckFlag)
                    "do not warn about possibly nonterminating code"
    , Option []     ["termination-depth"] (ReqArg terminationDepthFlag "N")
                    "allow termination checker to count decrease/increase upto N (default N=1)"
    , Option []     ["type-in-type"] (NoArg dontUniverseCheckFlag)
                    "ignore universe levels (this makes Agda inconsistent)"
    , Option []     ["omega-in-omega"] (NoArg omegaInOmegaFlag)
                    "enable typing rule Setω : Setω (this makes Agda inconsistent)"
    , Option []     ["cumulativity"] (NoArg cumulativityFlag)
                    "enable subtyping of universes (e.g. Set =< Set₁)"
    , Option []     ["no-cumulativity"] (NoArg noCumulativityFlag)
                    "disable subtyping of universes (default)"
    , Option []     ["prop"] (NoArg propFlag)
                    "enable the use of the Prop universe"
    , Option []     ["no-prop"] (NoArg noPropFlag)
                    "disable the use of the Prop universe (default)"
    , Option []     ["two-level"] (NoArg twoLevelFlag)
                    "enable the use of SSet* universes"
    , Option []     ["sized-types"] (NoArg sizedTypes)
                    "enable sized types (inconsistent with --guardedness)"
    , Option []     ["no-sized-types"] (NoArg noSizedTypes)
                    "disable sized types (default)"
    , Option []     ["cohesion"] (NoArg cohesionFlag)
                    "enable the cohesion modalities (in particular @flat)"
    , Option []     ["flat-split"] (NoArg flatSplitFlag)
                    "allow split on (@flat x : A) arguments (implies --cohesion)"
    , Option []     ["guardedness"] (NoArg guardedness)
                    "enable constructor-based guarded corecursion (inconsistent with --sized-types)"
    , Option []     ["no-guardedness"] (NoArg noGuardedness)
                    "disable constructor-based guarded corecursion (default)"
    , Option []     ["injective-type-constructors"] (NoArg injectiveTypeConstructorFlag)
                    "enable injective type constructors (makes Agda anti-classical and possibly inconsistent)"
    , Option []     ["no-universe-polymorphism"] (NoArg noUniversePolymorphismFlag)
                    "disable universe polymorphism"
    , Option []     ["universe-polymorphism"] (NoArg universePolymorphismFlag)
                    "enable universe polymorphism (default)"
    , Option []     ["irrelevant-projections"] (NoArg irrelevantProjectionsFlag)
                    "enable projection of irrelevant record fields and similar irrelevant definitions (inconsistent)"
    , Option []     ["no-irrelevant-projections"] (NoArg noIrrelevantProjectionsFlag)
                    "disable projection of irrelevant record fields and similar irrelevant definitions (default)"
    , Option []     ["experimental-irrelevance"] (NoArg experimentalIrrelevanceFlag)
                    "enable potentially unsound irrelevance features (irrelevant levels, irrelevant data matching)"
    , Option []     ["with-K"] (NoArg withKFlag)
                    "enable the K rule in pattern matching (default)"
    , Option []     ["cubical-compatible"] (NoArg cubicalCompatibleFlag)
                    "turn on generation of auxiliary code required for --cubical, implies --without-K"
    , Option []     ["without-K"] (NoArg withoutKFlag)
                    "turn on checks to make code compatible with HoTT (e.g. disabling the K rule). Implies --no-flat-split."
    , Option []     ["copatterns"] (NoArg copatternsFlag)
                    "enable definitions by copattern matching (default)"
    , Option []     ["no-copatterns"] (NoArg noCopatternsFlag)
                    "disable definitions by copattern matching"
    , Option []     ["no-pattern-matching"] (NoArg noPatternMatchingFlag)
                    "disable pattern matching completely"
    , Option []     ["exact-split"] (NoArg exactSplitFlag)
                    "require all clauses in a definition to hold as definitional equalities (unless marked CATCHALL)"
    , Option []     ["no-exact-split"] (NoArg noExactSplitFlag)
                    "do not require all clauses in a definition to hold as definitional equalities (default)"
    , Option []     ["no-eta-equality"] (NoArg noEtaFlag)
                    "default records to no-eta-equality"
    , Option []     ["no-forcing"] (NoArg noForcingFlag)
                    "disable the forcing analysis for data constructors (optimisation)"
    , Option []     ["no-projection-like"] (NoArg noProjectionLikeFlag)
                    "disable the analysis whether function signatures liken those of projections (optimisation)"
    , Option []     ["erase-record-parameters"] (NoArg eraseRecordParametersFlag)
                    "mark all parameters of record modules as erased"
    , Option []     ["no-erase-record-parameters"] (NoArg noEraseRecordParametersFlag)
                    "do mark all parameters of record modules as erased (default)"
    , Option []     ["rewriting"] (NoArg rewritingFlag)
                    "enable declaration and use of REWRITE rules"
    , Option []     ["local-confluence-check"] (NoArg $ confluenceCheckFlag LocalConfluenceCheck)
                    "enable checking of local confluence of REWRITE rules"
    , Option []     ["confluence-check"] (NoArg $ confluenceCheckFlag GlobalConfluenceCheck)
                    "enable global confluence checking of REWRITE rules (more restrictive than --local-confluence-check)"
    , Option []     ["no-confluence-check"] (NoArg noConfluenceCheckFlag)
                    "disable confluence checking of REWRITE rules (default)"
    , Option []     ["cubical"] (NoArg $ cubicalFlag CFull)
                    "enable cubical features (e.g. overloads lambdas for paths), implies --cubical-compatible"
    , Option []     ["erased-cubical"] (NoArg $ cubicalFlag CErased)
                    "enable cubical features (some only in erased settings), implies --cubical-compatible"
    , Option []     ["guarded"] (NoArg guardedFlag)
                    "enable @lock/@tick attributes"
    , lossyUnificationOption
    , Option []     ["postfix-projections"] (NoArg postfixProjectionsFlag)
                    "make postfix projection notation the default"
    , Option []     ["keep-pattern-variables"] (NoArg keepPatternVariablesFlag)
                    "don't replace variables with dot patterns during case splitting"
    , Option []     ["instance-search-depth"] (ReqArg instanceDepthFlag "N")
                    "set instance search depth to N (default: 500)"
    , Option []     ["overlapping-instances"] (NoArg overlappingInstancesFlag)
                    "consider recursive instance arguments during pruning of instance candidates"
    , Option []     ["no-overlapping-instances"] (NoArg noOverlappingInstancesFlag)
                    "don't consider recursive instance arguments during pruning of instance candidates (default)"
    , Option []     ["qualified-instances"] (NoArg qualifiedInstancesFlag)
                    "use instances with qualified names (default)"
    , Option []     ["no-qualified-instances"] (NoArg noQualifiedInstancesFlag)
                    "don't use instances with qualified names"
    , Option []     ["inversion-max-depth"] (ReqArg inversionMaxDepthFlag "N")
                    "set maximum depth for pattern match inversion to N (default: 50)"
    , Option []     ["safe"] (NoArg safeFlag)
                    "disable postulates, unsafe OPTION pragmas and primEraseEquality, implies --no-sized-types"
    , Option []     ["double-check"] (NoArg (doubleCheckFlag True))
                    "enable double-checking of all terms using the internal typechecker"
    , Option []     ["no-double-check"] (NoArg (doubleCheckFlag False))
                    "disable double-checking of terms (default)"
    , Option []     ["no-syntactic-equality"] (NoArg $ syntacticEqualityFlag (Just "0"))
                    "disable the syntactic equality shortcut in the conversion checker"
    , Option []     ["syntactic-equality"] (OptArg syntacticEqualityFlag "FUEL")
                    "give the syntactic equality shortcut FUEL units of fuel (default: unlimited)"
    , Option ['W']  ["warning"] (ReqArg warningModeFlag "FLAG")
                    ("set warning flags. See --help=warning.")
    , Option []     ["no-main"] (NoArg compileFlagNoMain)
                    "do not treat the requested module as the main module of a program when compiling"
    , Option []     ["caching"] (NoArg $ cachingFlag True)
                    "enable caching of typechecking (default)"
    , Option []     ["no-caching"] (NoArg $ cachingFlag False)
                    "disable caching of typechecking"
    , Option []     ["count-clusters"] (NoArg countClustersFlag)
                    ("count extended grapheme clusters when " ++
                     "generating LaTeX (note that this flag " ++
#ifdef COUNT_CLUSTERS
                     "is not enabled in all builds of Agda)"
#else
                     "has not been enabled in this build of Agda)"
#endif
                    )
    , Option []     ["auto-inline"] (NoArg autoInlineFlag)
                    "enable automatic compile-time inlining"
    , Option []     ["no-auto-inline"] (NoArg noAutoInlineFlag)
                    ("disable automatic compile-time inlining (default), " ++
                     "only definitions marked INLINE will be inlined")
    , Option []     ["no-print-pattern-synonyms"] (NoArg noPrintPatSynFlag)
                    "expand pattern synonyms when printing terms"
    , Option []     ["no-fast-reduce"] (NoArg noFastReduceFlag)
                    "disable reduction using the Agda Abstract Machine"
    , Option []     ["call-by-name"] (NoArg callByNameFlag)
                    "use call-by-name evaluation instead of call-by-need"
    , Option []     ["no-import-sorts"] (NoArg noImportSorts)
                    "disable the implicit import of Agda.Primitive using (Set; Prop) at the start of each top-level module"
    , Option []     ["no-load-primitives"] (NoArg noLoadPrimitivesFlag)
                    "disable loading of primitive modules at all (implies --no-import-sorts)"
    , Option []     ["allow-exec"] (NoArg allowExec)
                    "allow system calls to trusted executables with primExec"
    , Option []     ["save-metas"] (NoArg $ saveMetas True)
                    "save meta-variables"
    , Option []     ["no-save-metas"] (NoArg $ saveMetas False)
                    "do not save meta-variables (the default)"
    , Option []     ["keep-covering-clauses"] (NoArg keepCoveringClausesFlag)
                    "do not discard covering clauses (required for some external backends)"
    ]

lossyUnificationOption :: OptDescr (Flag PragmaOptions)
lossyUnificationOption =
      Option []     ["lossy-unification"] (NoArg firstOrderFlag)
                    "enable heuristically unifying `f es = f es'` by unifying `es = es'`, even when it could lose solutions"

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
      , lossyUnificationOption
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
      ucap = "Unrecognized " ++ plural unrecognized "option" ++ ":"
      ecap = plural errs "Option error" ++ ":"
      umsg = if null unrecognized then "" else unlines $
       ucap : map suggest unrecognized
      emsg = if null errs then "" else unlines $
       ecap : errs
      plural [_] x = x
      plural _   x = x ++ "s"

      -- Suggest alternatives that are at most 3 typos away

      longopts :: [String]
      longopts = map ("--" ++) $ concatMap (\ (Option _ long _ _) -> long) opts

      dist :: String -> String -> Int
      dist s t = restrictedDamerauLevenshteinDistance defaultEditCosts s t

      close :: String -> String -> Maybe (Int, String)
      close s t = let d = dist s t in if d <= 3 then Just (d, t) else Nothing

      closeopts :: String -> [(Int, String)]
      closeopts s = mapMaybe (close s) longopts

      alts :: String -> [[String]]
      alts s = map (map snd) $ groupOn fst $ closeopts s

      suggest :: String -> String
      suggest s = case alts s of
        []     -> s
        as : _ -> s ++ " (did you mean " ++ sugs as ++ " ?)"

      sugs :: [String] -> String
      sugs [a] = a
      sugs as  = "any of " ++ unwords as

-- | Parse options from an options pragma.
parsePragmaOptions
  :: [String]
     -- ^ Pragma options.
  -> CommandLineOptions
     -- ^ Command-line options which should be updated.
  -> OptM PragmaOptions
parsePragmaOptions argv opts = do
  ps <- getOptSimple argv (deadPragmaOptions ++ pragmaOptions)
          (\s _ -> throwError $ "Bad option in pragma: " ++ s)
          (optPragmaOptions opts)
  () <- checkOpts (opts { optPragmaOptions = ps })
  return ps

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
