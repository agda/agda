{-# LANGUAGE CPP       #-}
{-# LANGUAGE DataKinds #-}

module Agda.Interaction.Options.Base
    ( CommandLineOptions(..)
    , PragmaOptions(..)
    , OptionsPragma
    , Flag, OptM, runOptM, OptDescr(..), ArgDescr(..)
    , Verbosity, VerboseKey, VerboseLevel
    , WarningMode(..)
    , ConfluenceCheck(..)
    , UnicodeOrAscii(..)
    , checkOpts
    , parsePragmaOptions
    , parsePluginOptions
    , stripRTS
    , defaultOptions
    , defaultInteractionOptions
    , defaultVerbosity
    , defaultCutOff
    , defaultPragmaOptions
    , standardOptions_
    , unsafePragmaOptions
    , restartOptions
    , infectiveOptions
    , coinfectiveOptions
    , safeFlag
    , mapFlag
    , usage
    -- Reused by PandocAgda
    , inputFlag
    , standardOptions, deadStandardOptions
    , getOptSimple
    ) where

import Control.DeepSeq
import Control.Monad ( when, void )
import Control.Monad.Except ( Except, MonadError(throwError), runExcept )

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

import Agda.Utils.FileName      ( AbsolutePath )
import Agda.Utils.Functor       ( (<&>) )
import Agda.Utils.Lens          ( Lens', over )
import Agda.Utils.List          ( groupOn, initLast1, wordsBy )
import Agda.Utils.Pretty        ( singPlural )
import Agda.Utils.Trie          ( Trie )
import qualified Agda.Utils.Trie as Trie
import Agda.Utils.WithDefault

import Agda.Version

-- OptDescr is a Functor --------------------------------------------------

type VerboseKey   = String
type VerboseLevel = Int
type Verbosity    = Trie VerboseKey VerboseLevel

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
  , optTrustedExecutables             :: Map ExeName FilePath
  -- ^ Map names of trusted executables to absolute paths
  , optPrintAgdaDir          :: Bool
  , optPrintVersion          :: Bool
  , optPrintHelp             :: Maybe Help
  , optInteractive           :: Bool
      -- ^ Agda REPL (-I).
  , optGHCiInteraction       :: Bool
  , optJSONInteraction       :: Bool
  , optOptimSmashing         :: Bool
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
  }
  deriving (Show, Generic)

instance NFData CommandLineOptions

-- | Options which can be set in a pragma.

data PragmaOptions = PragmaOptions
  { optShowImplicit              :: Bool
  , optShowIrrelevant            :: Bool
  , optUseUnicode                :: UnicodeOrAscii
  , optVerbose                   :: Verbosity
  , optProp                      :: Bool
  , optTwoLevel                  :: WithDefault 'False
  , optAllowUnsolved             :: Bool
  , optAllowIncompleteMatch      :: Bool
  , optDisablePositivity         :: Bool
  , optTerminationCheck          :: Bool
  , optTerminationDepth          :: CutOff
    -- ^ Cut off structural order comparison at some depth in termination checker?
  , optCompletenessCheck         :: Bool
  , optUniverseCheck             :: Bool
  , optOmegaInOmega              :: Bool
  , optSubtyping                 :: WithDefault 'False
  , optCumulativity              :: Bool
  , optSizedTypes                :: WithDefault 'False
  , optGuardedness               :: WithDefault 'False
  , optInjectiveTypeConstructors :: Bool
  , optUniversePolymorphism      :: Bool
  , optIrrelevantProjections     :: Bool
  , optExperimentalIrrelevance   :: Bool  -- ^ irrelevant levels, irrelevant data matching
  , optWithoutK                  :: WithDefault 'False
  , optCopatterns                :: Bool  -- ^ Allow definitions by copattern matching?
  , optPatternMatching           :: Bool  -- ^ Is pattern matching allowed in the current file?
  , optExactSplit                :: Bool
  , optEta                       :: Bool
  , optForcing                   :: Bool  -- ^ Perform the forcing analysis on data constructors?
  , optProjectionLike            :: Bool  -- ^ Perform the projection-likeness analysis on functions?
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
  , optSyntacticEquality         :: Bool  -- ^ Should conversion checker use syntactic equality shortcut?
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
  , optFlatSplit                 :: Bool
     -- ^ Can we split on a (@flat x : A) argument?
  , optImportSorts               :: Bool
     -- ^ Should every top-level module start with an implicit statement
     --   @open import Agda.Primitive using (Set; Prop)@?
  , optAllowExec                 :: Bool
  , optShowIdentitySubstitutions :: Bool
    -- ^ Show identity substitutions when pretty-printing terms
    --   (i.e. always show all arguments of a metavariable)
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

defaultVerbosity :: Verbosity
defaultVerbosity = Trie.singleton [] 1

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
  , optTrustedExecutables    = Map.empty
  , optPrintAgdaDir          = False
  , optPrintVersion          = False
  , optPrintHelp             = Nothing
  , optInteractive           = False
  , optGHCiInteraction       = False
  , optJSONInteraction       = False
  , optOptimSmashing         = True
  , optCompileDir            = Nothing
  , optGenerateVimFile       = False
  , optIgnoreInterfaces      = False
  , optIgnoreAllInterfaces   = False
  , optLocalInterfaces       = False
  , optPragmaOptions         = defaultPragmaOptions
  , optOnlyScopeChecking     = False
  }

defaultPragmaOptions :: PragmaOptions
defaultPragmaOptions = PragmaOptions
  { optShowImplicit              = False
  , optShowIrrelevant            = False
  , optUseUnicode                = UnicodeOk
  , optVerbose                   = defaultVerbosity
  , optProp                      = False
  , optTwoLevel                  = Default
  , optExperimentalIrrelevance   = False
  , optIrrelevantProjections     = False -- off by default in > 2.5.4, see issue #2170
  , optAllowUnsolved             = False
  , optAllowIncompleteMatch      = False
  , optDisablePositivity         = False
  , optTerminationCheck          = True
  , optTerminationDepth          = defaultCutOff
  , optCompletenessCheck         = True
  , optUniverseCheck             = True
  , optOmegaInOmega              = False
  , optSubtyping                 = Default
  , optCumulativity              = False
  , optSizedTypes                = Default
  , optGuardedness               = Default
  , optInjectiveTypeConstructors = False
  , optUniversePolymorphism      = True
  , optWithoutK                  = Default
  , optCopatterns                = True
  , optPatternMatching           = True
  , optExactSplit                = False
  , optEta                       = True
  , optForcing                   = True
  , optProjectionLike            = True
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
  , optSyntacticEquality         = True
  , optWarningMode               = defaultWarningMode
  , optCompileNoMain             = False
  , optCaching                   = True
  , optCountClusters             = False
  , optAutoInline                = False
  , optPrintPatternSynonyms      = True
  , optFastReduce                = True
  , optCallByName                = False
  , optConfluenceCheck           = Nothing
  , optFlatSplit                 = True
  , optImportSorts               = True
  , optAllowExec                 = False
  , optShowIdentitySubstitutions = False
  }

type OptM = Except String

runOptM :: Monad m => OptM opts -> m (Either String opts)
runOptM = pure . runExcept

{- | @f :: Flag opts@  is an action on the option record that results from
     parsing an option.  @f opts@ produces either an error message or an
     updated options record
-}
type Flag opts = opts -> OptM opts

-- | Checks that the given options are consistent.

checkOpts :: Flag CommandLineOptions
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
  return opts

-- | Check for unsafe pragmas. Gives a list of used unsafe flags.

unsafePragmaOptions :: CommandLineOptions -> PragmaOptions -> [String]
unsafePragmaOptions clo opts =
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
  [ "--cubical and --with-K"                     | optCubical opts == Just CFull
                                                 , not (collapseDefault $ optWithoutK opts) ] ++
  [ "--erased-cubical and --with-K"              | optCubical opts == Just CErased
                                                 , not (collapseDefault $ optWithoutK opts) ] ++
  [ "--cumulativity"                             | optCumulativity opts              ] ++
  [ "--allow-exec"                               | optAllowExec opts                 ] ++
  []

-- | If any these options have changed, then the file will be
--   rechecked. Boolean options are negated to mention non-default
--   options, where possible.

restartOptions :: [(PragmaOptions -> RestartCodomain, String)]
restartOptions =
  [ (C . optTerminationDepth, "--termination-depth")
  , (B . (/= UnicodeOk) . optUseUnicode, "--no-unicode")
  , (B . optAllowUnsolved, "--allow-unsolved-metas")
  , (B . optAllowIncompleteMatch, "--allow-incomplete-matches")
  , (B . optDisablePositivity, "--no-positivity-check")
  , (B . optTerminationCheck,  "--no-termination-check")
  , (B . not . optUniverseCheck, "--type-in-type")
  , (B . optOmegaInOmega, "--omega-in-omega")
  , (B . collapseDefault . optSubtyping, "--subtyping")
  , (B . optCumulativity, "--cumulativity")
  , (B . collapseDefault . optSizedTypes, "--no-sized-types")
  , (B . collapseDefault . optGuardedness, "--no-guardedness")
  , (B . optInjectiveTypeConstructors, "--injective-type-constructors")
  , (B . optProp, "--prop")
  , (B . collapseDefault . optTwoLevel, "--two-level")
  , (B . not . optUniversePolymorphism, "--no-universe-polymorphism")
  , (B . optIrrelevantProjections, "--irrelevant-projections")
  , (B . optExperimentalIrrelevance, "--experimental-irrelevance")
  , (B . collapseDefault . optWithoutK, "--without-K")
  , (B . optExactSplit, "--exact-split")
  , (B . not . optEta, "--no-eta-equality")
  , (B . optRewriting, "--rewriting")
  , (B . (== Just CFull) . optCubical, "--cubical")
  , (B . (== Just CErased) . optCubical, "--erased-cubical")
  , (B . optGuarded, "--guarded")
  , (B . optOverlappingInstances, "--overlapping-instances")
  , (B . optQualifiedInstances, "--qualified-instances")
  , (B . not . optQualifiedInstances, "--no-qualified-instances")
  , (B . optSafe, "--safe")
  , (B . optDoubleCheck, "--double-check")
  , (B . not . optSyntacticEquality, "--no-syntactic-equality")
  , (B . not . optAutoInline, "--no-auto-inline")
  , (B . not . optFastReduce, "--no-fast-reduce")
  , (B . optCallByName, "--call-by-name")
  , (I . optInstanceSearchDepth, "--instance-search-depth")
  , (I . optInversionMaxDepth, "--inversion-max-depth")
  , (W . optWarningMode, "--warning")
  , (B . (== Just LocalConfluenceCheck) . optConfluenceCheck, "--local-confluence-check")
  , (B . (== Just GlobalConfluenceCheck) . optConfluenceCheck, "--confluence-check")
  , (B . not . optImportSorts, "--no-import-sorts")
  , (B . optAllowExec, "--allow-exec")
  ]

-- to make all restart options have the same type
data RestartCodomain = C CutOff | B Bool | I Int | W WarningMode
  deriving Eq

-- | An infective option is an option that if used in one module, must
--   be used in all modules that depend on this module.
--
-- Note that @--cubical@ and @--erased-cubical@ are \"jointly
-- infective\": if one of them is used in one module, then one or the
-- other must be used in all modules that depend on this module.

infectiveOptions :: [(PragmaOptions -> Bool, String)]
infectiveOptions =
  [ (isJust . optCubical, "--cubical/--erased-cubical")
  , (optGuarded, "--guarded")
  , (optProp, "--prop")
  , (collapseDefault . optTwoLevel, "--two-level")
  , (optRewriting, "--rewriting")
  , (collapseDefault . optSizedTypes, "--sized-types")
  , (collapseDefault . optGuardedness, "--guardedness")
  ]

-- | A coinfective option is an option that if used in one module, must
--   be used in all modules that this module depends on.

coinfectiveOptions :: [(PragmaOptions -> Bool, String)]
coinfectiveOptions =
  [ (optSafe, "--safe")
  , (collapseDefault . optWithoutK, "--without-K")
  , (not . optUniversePolymorphism, "--no-universe-polymorphism")
  , (not . collapseDefault . optSubtyping, "--no-subtyping")
  , (not . optCumulativity, "--no-cumulativity")
  ]

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

flatSplitFlag :: Flag PragmaOptions
flatSplitFlag o = return $ o { optFlatSplit = True }

noFlatSplitFlag :: Flag PragmaOptions
noFlatSplitFlag o = return $ o { optFlatSplit = False }

doubleCheckFlag :: Bool -> Flag PragmaOptions
doubleCheckFlag b o = return $ o { optDoubleCheck = b }

noSyntacticEqualityFlag :: Flag PragmaOptions
noSyntacticEqualityFlag o = return $ o { optSyntacticEquality = False }

noSortComparisonFlag :: Flag PragmaOptions
noSortComparisonFlag o = return o

sharingFlag :: Bool -> Flag CommandLineOptions
sharingFlag _ _ = throwError $
  "Feature --sharing has been removed (in favor of the Agda abstract machine)."

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

asciiOnlyFlag :: Flag PragmaOptions
asciiOnlyFlag o = return $ UNSAFE.unsafePerformIO $ do
  unsafeSetUnicodeOrAscii AsciiOnly
  return $ o { optUseUnicode = AsciiOnly }

ghciInteractionFlag :: Flag CommandLineOptions
ghciInteractionFlag o = return $ o { optGHCiInteraction = True }

jsonInteractionFlag :: Flag CommandLineOptions
jsonInteractionFlag o = return $ o { optJSONInteraction = True }

vimFlag :: Flag CommandLineOptions
vimFlag o = return $ o { optGenerateVimFile = True }

onlyScopeCheckingFlag :: Flag CommandLineOptions
onlyScopeCheckingFlag o = return $ o { optOnlyScopeChecking = True }

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

-- The option was removed. See Issue 1918.
dontCompletenessCheckFlag :: Flag PragmaOptions
dontCompletenessCheckFlag _ =
  throwError "The --no-coverage-check option has been removed."

dontUniverseCheckFlag :: Flag PragmaOptions
dontUniverseCheckFlag o = return $ o { optUniverseCheck = False }

omegaInOmegaFlag :: Flag PragmaOptions
omegaInOmegaFlag o = return $ o { optOmegaInOmega = True }

subtypingFlag :: Flag PragmaOptions
subtypingFlag o = return $ o { optSubtyping = Value True }

noSubtypingFlag :: Flag PragmaOptions
noSubtypingFlag o = return $ o { optSubtyping = Value False }

cumulativityFlag :: Flag PragmaOptions
cumulativityFlag o =
  return $ o { optCumulativity = True
             , optSubtyping    = setDefault True $ optSubtyping o
             }

noCumulativityFlag :: Flag PragmaOptions
noCumulativityFlag o = return $ o { optCumulativity = False }

--UNUSED Liang-Ting Chen 2019-07-16
--etaFlag :: Flag PragmaOptions
--etaFlag o = return $ o { optEta = True }

noEtaFlag :: Flag PragmaOptions
noEtaFlag o = return $ o { optEta = False }

sizedTypes :: Flag PragmaOptions
sizedTypes o =
  return $ o { optSizedTypes = Value True
             --, optSubtyping  = setDefault True $ optSubtyping o
             }

noSizedTypes :: Flag PragmaOptions
noSizedTypes o = return $ o { optSizedTypes = Value False }

guardedness :: Flag PragmaOptions
guardedness o = return $ o { optGuardedness = Value True }

noGuardedness :: Flag PragmaOptions
noGuardedness o = return $ o { optGuardedness = Value False }

injectiveTypeConstructorFlag :: Flag PragmaOptions
injectiveTypeConstructorFlag o = return $ o { optInjectiveTypeConstructors = True }

guardingTypeConstructorFlag :: Flag PragmaOptions
guardingTypeConstructorFlag _ = throwError $
  "Experimental feature --guardedness-preserving-type-constructors has been removed."

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
withoutKFlag o = return $ o { optWithoutK = Value True }

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

cubicalFlag
  :: Cubical  -- ^ Which variant of Cubical Agda?
  -> Flag PragmaOptions
cubicalFlag variant o = do
  let withoutK = optWithoutK o
  return $ o { optCubical  = Just variant
             , optWithoutK = setDefault True withoutK
             , optTwoLevel = setDefault True $ optTwoLevel o
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
        return $ o { optVerbose = Trie.insert k n $ optVerbose o }
  where
    parseVerbose :: String -> OptM ([VerboseKey], VerboseLevel)
    parseVerbose s = case wordsBy (`elem` (":." :: String)) s of
      []  -> usage
      s0:ss0 -> do
        let (ss, s) = initLast1 s0 ss0
        n <- maybe usage return $ readMaybe s
        return (ss, n)
    usage = throwError "argument to verbose should be on the form x.y.z:N or N"

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

integerArgument :: String -> String -> OptM Int
integerArgument flag s = maybe usage return $ readMaybe s
  where
  usage = throwError $ "option '" ++ flag ++ "' requires an integer argument"

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

    , Option []     ["compile-dir"] (ReqArg compileDirFlag "DIR")
                    ("directory for compiler output (default: the project root)")

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
    ] ++ map (fmap lensPragmaOptions) pragmaOptions

-- | Defined locally here since module ''Agda.Interaction.Options.Lenses''
--   has cyclic dependency.
lensPragmaOptions :: Lens' PragmaOptions CommandLineOptions
lensPragmaOptions f st = f (optPragmaOptions st) <&> \ opts -> st { optPragmaOptions = opts }

-- | Command line options of previous versions of Agda.
--   Should not be listed in the usage info, put parsed by GetOpt for good error messaging.
deadStandardOptions :: [OptDescr (Flag CommandLineOptions)]
deadStandardOptions =
    [ Option []     ["sharing"] (NoArg $ sharingFlag True)
                    "DEPRECATED: does nothing"
    , Option []     ["no-sharing"] (NoArg $ sharingFlag False)
                    "DEPRECATED: does nothing"
    , Option []     ["ignore-all-interfaces"] (NoArg ignoreAllInterfacesFlag) -- not deprecated! Just hidden
                    "ignore all interface files (re-type check everything, including builtin files)"
    ] ++ map (fmap lensPragmaOptions) deadPragmaOptions

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
    , Option []     ["subtyping"] (NoArg subtypingFlag)
                    "enable subtyping rules in general (e.g. for irrelevance and erasure)"
    , Option []     ["no-subtyping"] (NoArg noSubtypingFlag)
                    "disable subtyping rules in general (e.g. for irrelevance and erasure) (default)"
    , Option []     ["cumulativity"] (NoArg cumulativityFlag)
                    "enable subtyping of universes (e.g. Set =< Set₁) (implies --subtyping)"
    , Option []     ["no-cumulativity"] (NoArg noCumulativityFlag)
                    "disable subtyping of universes (default)"
    , Option []     ["prop"] (NoArg propFlag)
                    "enable the use of the Prop universe"
    , Option []     ["no-prop"] (NoArg noPropFlag)
                    "disable the use of the Prop universe (default)"
    , Option []     ["two-level"] (NoArg twoLevelFlag)
                    "enable the use of SSet* universes"
    , Option []     ["sized-types"] (NoArg sizedTypes)
                    "enable sized types (default, inconsistent with --guardedness, implies --subtyping)"
    , Option []     ["no-sized-types"] (NoArg noSizedTypes)
                    "disable sized types"
    , Option []     ["flat-split"] (NoArg flatSplitFlag)
                    "allow split on (@flat x : A) arguments (default)"
    , Option []     ["no-flat-split"] (NoArg noFlatSplitFlag)
                    "disable split on (@flat x : A) arguments"
    , Option []     ["guardedness"] (NoArg guardedness)
                    "enable constructor-based guarded corecursion (default, inconsistent with --sized-types)"
    , Option []     ["no-guardedness"] (NoArg noGuardedness)
                    "disable constructor-based guarded corecursion"
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
    , Option []     ["without-K"] (NoArg withoutKFlag)
                    "disable the K rule in pattern matching"
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
    , Option []     ["rewriting"] (NoArg rewritingFlag)
                    "enable declaration and use of REWRITE rules"
    , Option []     ["local-confluence-check"] (NoArg $ confluenceCheckFlag LocalConfluenceCheck)
                    "enable checking of local confluence of REWRITE rules"
    , Option []     ["confluence-check"] (NoArg $ confluenceCheckFlag GlobalConfluenceCheck)
                    "enable global confluence checking of REWRITE rules (more restrictive than --local-confluence-check)"
    , Option []     ["no-confluence-check"] (NoArg noConfluenceCheckFlag)
                    "disable confluence checking of REWRITE rules (default)"
    , Option []     ["cubical"] (NoArg $ cubicalFlag CFull)
                    "enable cubical features (e.g. overloads lambdas for paths), implies --without-K"
    , Option []     ["erased-cubical"] (NoArg $ cubicalFlag CErased)
                    "enable cubical features (some only in erased settings), implies --without-K"
    , Option []     ["guarded"] (NoArg guardedFlag)
                    "enable @lock/@tick attributes"
    , Option []     ["experimental-lossy-unification"] (NoArg firstOrderFlag)
                    "enable heuristically unifying `f es = f es'` by unifying `es = es'`, even when it could lose solutions."
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
    , Option []     ["no-syntactic-equality"] (NoArg noSyntacticEqualityFlag)
                    "disable the syntactic equality shortcut in the conversion checker"
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
    , Option []     ["allow-exec"] (NoArg allowExec)
                    "allow system calls to trusted executables with primExec"
    ]

-- | Pragma options of previous versions of Agda.
--   Should not be listed in the usage info, put parsed by GetOpt for good error messaging.
deadPragmaOptions :: [OptDescr (Flag PragmaOptions)]
deadPragmaOptions =
    [ Option []     ["guardedness-preserving-type-constructors"] (NoArg guardingTypeConstructorFlag)
                    "treat type constructors as inductive constructors when checking productivity"
    , Option []     ["no-coverage-check"] (NoArg dontCompletenessCheckFlag)
                    "the option has been removed"
    , Option []     ["no-sort-comparison"] (NoArg noSortComparisonFlag)
                    "disable the comparison of sorts when checking conversion of types"
    ]

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

{- No longer used in favour of parseBackendOptions in Agda.Compiler.Backend
-- | Parse the standard options.
parseStandardOptions :: [String] -> OptM CommandLineOptions
parseStandardOptions argv = parseStandardOptions' argv defaultOptions

parseStandardOptions' :: [String] -> Flag CommandLineOptions
parseStandardOptions' argv opts = do
  opts <- getOptSimple (stripRTS argv) (deadStandardOptions ++ standardOptions) inputFlag opts
  checkOpts opts
-}

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
  _ <- checkOpts (opts { optPragmaOptions = ps })
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
