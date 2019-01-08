{-# LANGUAGE CPP #-}

module Agda.Interaction.Options
    ( CommandLineOptions(..)
    , PragmaOptions(..)
    , OptionsPragma
    , Flag, OptM, runOptM, OptDescr(..), ArgDescr(..)
    , Verbosity
    , HtmlHighlight(..)
    , WarningMode(..)
    , checkOpts
    , parseStandardOptions, parseStandardOptions'
    , parsePragmaOptions
    , parsePluginOptions
    , defaultOptions
    , defaultInteractionOptions
    , defaultVerbosity
    , defaultCutOff
    , defaultPragmaOptions
    , standardOptions_
    , unsafePragmaOptions
    , safeFlag
    , mapFlag
    , usage
    , defaultLibDir
    -- Reused by PandocAgda
    , inputFlag
    , standardOptions
    , getOptSimple
    ) where

import Control.Monad            ( (>=>), when )
import Control.Monad.Trans

import Data.IORef
import Data.Either
import Data.Function
import Data.Maybe
import Data.List                ( isSuffixOf , intercalate )
import Data.Set                 ( Set )
import qualified Data.Set as Set

import System.Console.GetOpt    ( getOpt', usageInfo, ArgOrder(ReturnInOrder)
                                , OptDescr(..), ArgDescr(..)
                                )
import System.Directory         ( doesFileExist, doesDirectoryExist )

import Text.EditDistance

import Agda.Termination.CutOff  ( CutOff(..) )

import Agda.Interaction.Library
import Agda.Interaction.Options.Help
import Agda.Interaction.Options.IORefs
import Agda.Interaction.Options.Warnings

import Agda.Utils.Except
  ( ExceptT
  , MonadError(catchError, throwError)
  , runExceptT
  )

import Agda.Utils.FileName      ( absolute, AbsolutePath, filePath )
import Agda.Utils.Functor       ( (<&>) )
import Agda.Utils.Lens          ( Lens', over )
import Agda.Utils.List          ( groupOn, wordsBy )
import Agda.Utils.Monad         ( ifM, readM )
import Agda.Utils.String        ( indent )
import Agda.Utils.Trie          ( Trie )
import qualified Agda.Utils.Trie as Trie

import Agda.Version
-- Paths_Agda.hs is in $(BUILD_DIR)/build/autogen/.
import Paths_Agda ( getDataFileName )

import qualified System.IO.Unsafe as UNSAFE (unsafePerformIO)

-- OptDescr is a Functor --------------------------------------------------

type Verbosity = Trie String Int

data HtmlHighlight = HighlightAll | HighlightCode | HighlightAuto
  deriving (Show, Eq)

-- Don't forget to update
--   doc/user-manual/tools/command-line-options.rst
-- if you make changes to the command-line options!

data CommandLineOptions = Options
  { optProgramName      :: String
  , optInputFile        :: Maybe FilePath
  , optIncludePaths     :: [FilePath]
  , optAbsoluteIncludePaths :: [AbsolutePath]
  , optLibraries        :: [LibName]
  , optOverrideLibrariesFile :: Maybe FilePath
  -- ^ Use this (if Just) instead of .agda/libraries
  , optDefaultLibs      :: Bool
  -- ^ Use ~/.agda/defaults
  , optUseLibs          :: Bool
  -- ^ look for .agda-lib files
  , optShowVersion      :: Bool
  , optShowHelp         :: Maybe Help
  , optInteractive      :: Bool
  , optGHCiInteraction  :: Bool
  , optJSONInteraction  :: Bool
  , optOptimSmashing    :: Bool
  , optCompileDir       :: Maybe FilePath
  -- ^ In the absence of a path the project root is used.
  , optGenerateVimFile  :: Bool
  , optGenerateLaTeX    :: Bool
  , optGenerateHTML     :: Bool
  , optHTMLHighlight    :: HtmlHighlight
  , optDependencyGraph  :: Maybe FilePath
  , optLaTeXDir         :: FilePath
  , optHTMLDir          :: FilePath
  , optCSSFile          :: Maybe FilePath
  , optIgnoreInterfaces :: Bool
  , optForcing          :: Bool
  , optPragmaOptions    :: PragmaOptions
  , optOnlyScopeChecking :: Bool
    -- ^ Should the top-level module only be scope-checked, and not
    --   type-checked?
  }
  deriving Show

-- | Options which can be set in a pragma.

data PragmaOptions = PragmaOptions
  { optShowImplicit              :: Bool
  , optShowIrrelevant            :: Bool
  , optUseUnicode                :: Bool
  , optVerbose                   :: Verbosity
  , optProp                      :: Bool
  , optAllowUnsolved             :: Bool
  , optDisablePositivity         :: Bool
  , optTerminationCheck          :: Bool
  , optTerminationDepth          :: CutOff
    -- ^ Cut off structural order comparison at some depth in termination checker?
  , optCompletenessCheck         :: Bool
  , optUniverseCheck             :: Bool
  , optOmegaInOmega              :: Bool
  , optSizedTypes                :: Bool
  , optGuardedness               :: Bool
  , optInjectiveTypeConstructors :: Bool
  , optUniversePolymorphism      :: Bool
  , optIrrelevantProjections     :: Bool
  , optExperimentalIrrelevance   :: Bool  -- ^ irrelevant levels, irrelevant data matching
  , optWithoutK                  :: Bool
  , optCopatterns                :: Bool  -- ^ Allow definitions by copattern matching?
  , optPatternMatching           :: Bool  -- ^ Is pattern matching allowed in the current file?
  , optExactSplit                :: Bool
  , optEta                       :: Bool
  , optRewriting                 :: Bool  -- ^ Can rewrite rules be added and used?
  , optCubical                   :: Bool
  , optPostfixProjections        :: Bool
      -- ^ Should system generated projections 'ProjSystem' be printed
      --   postfix (True) or prefix (False).
  , optInstanceSearchDepth       :: Int
  , optOverlappingInstances      :: Bool
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
  }
  deriving (Show, Eq)

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
  , optInputFile        = Nothing
  , optIncludePaths     = []
  , optAbsoluteIncludePaths = []
  , optLibraries        = []
  , optOverrideLibrariesFile = Nothing
  , optDefaultLibs      = True
  , optUseLibs          = True
  , optShowVersion      = False
  , optShowHelp         = Nothing
  , optInteractive      = False
  , optGHCiInteraction  = False
  , optJSONInteraction  = False
  , optOptimSmashing    = True
  , optCompileDir       = Nothing
  , optGenerateVimFile  = False
  , optGenerateLaTeX    = False
  , optGenerateHTML     = False
  , optHTMLHighlight    = HighlightAll
  , optDependencyGraph  = Nothing
  , optLaTeXDir         = defaultLaTeXDir
  , optHTMLDir          = defaultHTMLDir
  , optCSSFile          = Nothing
  , optIgnoreInterfaces = False
  , optForcing          = True
  , optPragmaOptions    = defaultPragmaOptions
  , optOnlyScopeChecking = False
  }

defaultPragmaOptions :: PragmaOptions
defaultPragmaOptions = PragmaOptions
  { optShowImplicit              = False
  , optShowIrrelevant            = False
  , optUseUnicode                = True
  , optVerbose                   = defaultVerbosity
  , optProp                      = False
  , optExperimentalIrrelevance   = False
  , optIrrelevantProjections     = False -- off by default in > 2.5.4, see issue #2170
  , optAllowUnsolved             = False
  , optDisablePositivity         = False
  , optTerminationCheck          = True
  , optTerminationDepth          = defaultCutOff
  , optCompletenessCheck         = True
  , optUniverseCheck             = True
  , optOmegaInOmega              = False
  , optSizedTypes                = True
  , optGuardedness               = True
  , optInjectiveTypeConstructors = False
  , optUniversePolymorphism      = True
  , optWithoutK                  = False
  , optCopatterns                = True
  , optPatternMatching           = True
  , optExactSplit                = False
  , optEta                       = True
  , optRewriting                 = False
  , optCubical                   = False
  , optPostfixProjections        = False
  , optInstanceSearchDepth       = 500
  , optOverlappingInstances      = False
  , optInversionMaxDepth         = 50
  , optSafe                      = False
  , optDoubleCheck               = False
  , optSyntacticEquality         = True
  , optWarningMode               = defaultWarningMode
  , optCompileNoMain             = False
  , optCaching                   = True
  , optCountClusters             = False
  , optAutoInline                = True
  , optPrintPatternSynonyms      = True
  , optFastReduce                = True
  }

-- | The default termination depth.

defaultCutOff :: CutOff
defaultCutOff = CutOff 0 -- minimum value

-- | The default output directory for LaTeX.

defaultLaTeXDir :: String
defaultLaTeXDir = "latex"

-- | The default output directory for HTML.

defaultHTMLDir :: String
defaultHTMLDir = "html"

type OptM = ExceptT String IO

runOptM :: OptM a -> IO (Either String a)
runOptM = runExceptT

{- | @f :: Flag opts@  is an action on the option record that results from
     parsing an option.  @f opts@ produces either an error message or an
     updated options record
-}
type Flag opts = opts -> OptM opts

-- | Checks that the given options are consistent.

checkOpts :: Flag CommandLineOptions
checkOpts opts
  | htmlRelated = throwError htmlRelatedMessage
  | not (matches [optGHCiInteraction, optJSONInteraction, isJust . optInputFile] <= 1) =
      throwError "Choose at most one: input file, --interactive, or --interaction-json.\n"
  | or [ p opts && matches ps > 1 | (p, ps) <- exclusive ] =
      throwError exclusiveMessage
  | otherwise = return opts
  where
  matches = length . filter ($ opts)
  optionChanged opt = ((/=) `on` opt) opts defaultOptions

  atMostOne =
    [ optGenerateHTML
    , isJust . optDependencyGraph
    ] ++
    map fst exclusive

  exclusive =
    [ ( optOnlyScopeChecking
      , optGenerateVimFile :
        atMostOne
      )
    , ( optInteractive
      , optGenerateLaTeX : atMostOne
      )
    , ( optGHCiInteraction
      , optGenerateLaTeX : atMostOne
      )
    , ( optJSONInteraction
      , optGenerateLaTeX : atMostOne
      )
    ]

  exclusiveMessage = unlines $
    [ "The options --interactive, --interaction, --interaction-json and"
    , "--only-scope-checking cannot be combined with each other or"
    , "with --html or --dependency-graph. Furthermore"
    , "--interactive and --interaction cannot be combined with"
    , "--latex, and --only-scope-checking cannot be combined with"
    , "--vim."
    ]

  htmlRelated = not (optGenerateHTML opts) &&
    (  optionChanged optHTMLDir
    || optionChanged optHTMLHighlight
    || optionChanged optCSSFile
    )

  htmlRelatedMessage = unlines $
    [ "The options --html-highlight, --css-dir and --html-dir"
    , "only be used along with --html flag."
    ]

-- | Check for unsafe pragmas. Gives a list of used unsafe flags.

unsafePragmaOptions :: PragmaOptions -> [String]
unsafePragmaOptions opts =
  [ "--allow-unsolved-metas"                     | optAllowUnsolved opts             ] ++
  [ "--no-positivity-check"                      | optDisablePositivity opts         ] ++
  [ "--no-termination-check"                     | not (optTerminationCheck opts)    ] ++
  [ "--type-in-type"                             | not (optUniverseCheck opts)       ] ++
  [ "--omega-in-omega"                           | optOmegaInOmega opts              ] ++
  -- [ "--sized-types"                              | optSizedTypes opts                ] ++
  [ "--sized-types and --guardedness"            | optSizedTypes opts, optGuardedness opts ] ++
  [ "--injective-type-constructors"              | optInjectiveTypeConstructors opts ] ++
  [ "--irrelevant-projections"                   | optIrrelevantProjections opts     ] ++
  [ "--experimental-irrelevance"                 | optExperimentalIrrelevance opts   ] ++
  [ "--rewriting"                                | optRewriting opts                 ] ++
  [ "--cubical and --with-K"                     | optCubical opts, not $ optWithoutK opts ] ++
  []

inputFlag :: FilePath -> Flag CommandLineOptions
inputFlag f o =
    case optInputFile o of
        Nothing  -> return $ o { optInputFile = Just f }
        Just _   -> throwError "only one input file allowed"

versionFlag :: Flag CommandLineOptions
versionFlag o = return $ o { optShowVersion = True }

helpFlag :: Maybe String -> Flag CommandLineOptions
helpFlag Nothing    o = return $ o { optShowHelp = Just GeneralHelp }
helpFlag (Just str) o = case string2HelpTopic str of
  Just hpt -> return $ o { optShowHelp = Just (HelpFor hpt) }
  Nothing -> throwError $ "unknown help topic " ++ str ++ " (available: " ++
                           intercalate ", " (map fst allHelpTopics) ++ ")"

safeFlag :: Flag PragmaOptions
safeFlag o = return $ o { optSafe        = True
                        , optGuardedness = False
                        , optSizedTypes  = False
                        }

doubleCheckFlag :: Flag PragmaOptions
doubleCheckFlag o = return $ o { optDoubleCheck = True }

noSyntacticEqualityFlag :: Flag PragmaOptions
noSyntacticEqualityFlag o = return $ o { optSyntacticEquality = False }

sharingFlag :: Bool -> Flag CommandLineOptions
sharingFlag _ _ = throwError $
  "Feature --sharing has been removed (in favor of the Agda abstract machine)."

cachingFlag :: Bool -> Flag PragmaOptions
cachingFlag b o = return $ o { optCaching = b }

propFlag :: Flag PragmaOptions
propFlag o = return $ o { optProp = True }

noPropFlag :: Flag PragmaOptions
noPropFlag o = return $ o { optProp = False }

experimentalIrrelevanceFlag :: Flag PragmaOptions
experimentalIrrelevanceFlag o = return $ o { optExperimentalIrrelevance = True }

irrelevantProjectionsFlag :: Flag PragmaOptions
irrelevantProjectionsFlag o = return $ o { optIrrelevantProjections = True }

noIrrelevantProjectionsFlag :: Flag PragmaOptions
noIrrelevantProjectionsFlag o = return $ o { optIrrelevantProjections = False }

ignoreInterfacesFlag :: Flag CommandLineOptions
ignoreInterfacesFlag o = return $ o { optIgnoreInterfaces = True }

allowUnsolvedFlag :: Flag PragmaOptions
allowUnsolvedFlag o = do
  let upd = over warningSet (Set.\\ unsolvedWarnings)
  return $ o { optAllowUnsolved = True
             , optWarningMode   = upd (optWarningMode o)
             }

showImplicitFlag :: Flag PragmaOptions
showImplicitFlag o = return $ o { optShowImplicit = True }

showIrrelevantFlag :: Flag PragmaOptions
showIrrelevantFlag o = return $ o { optShowIrrelevant = True }

asciiOnlyFlag :: Flag PragmaOptions
asciiOnlyFlag o = do
  lift $ writeIORef unicodeOrAscii AsciiOnly
  return $ o { optUseUnicode = False }

ghciInteractionFlag :: Flag CommandLineOptions
ghciInteractionFlag o = return $ o { optGHCiInteraction = True }

jsonInteractionFlag :: Flag CommandLineOptions
jsonInteractionFlag o = return $ o { optJSONInteraction = True }

vimFlag :: Flag CommandLineOptions
vimFlag o = return $ o { optGenerateVimFile = True }

latexFlag :: Flag CommandLineOptions
latexFlag o = return $ o { optGenerateLaTeX = True }

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

noPrintPatSynFlag :: Flag PragmaOptions
noPrintPatSynFlag o = return $ o { optPrintPatternSynonyms = False }

noFastReduceFlag :: Flag PragmaOptions
noFastReduceFlag o = return $ o { optFastReduce = False }

latexDirFlag :: FilePath -> Flag CommandLineOptions
latexDirFlag d o = return $ o { optLaTeXDir = d }

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

etaFlag :: Flag PragmaOptions
etaFlag o = return $ o { optEta = True }

noEtaFlag :: Flag PragmaOptions
noEtaFlag o = return $ o { optEta = False }

sizedTypes :: Flag PragmaOptions
sizedTypes o = return $ o { optSizedTypes = True }

noSizedTypes :: Flag PragmaOptions
noSizedTypes o = return $ o { optSizedTypes = False }

guardedness :: Flag PragmaOptions
guardedness o = return $ o { optGuardedness = True
                        -- , optSizedTypes  = False
                           }

noGuardedness :: Flag PragmaOptions
noGuardedness o = return $ o { optGuardedness = False }

injectiveTypeConstructorFlag :: Flag PragmaOptions
injectiveTypeConstructorFlag o = return $ o { optInjectiveTypeConstructors = True }

guardingTypeConstructorFlag :: Flag PragmaOptions
guardingTypeConstructorFlag _ = throwError $
  "Experimental feature --guardedness-preserving-type-constructors has been removed."

universePolymorphismFlag :: Flag PragmaOptions
universePolymorphismFlag o = return $ o { optUniversePolymorphism = True }

noUniversePolymorphismFlag :: Flag PragmaOptions
noUniversePolymorphismFlag  o = return $ o { optUniversePolymorphism = False }

noForcingFlag :: Flag CommandLineOptions
noForcingFlag o = return $ o { optForcing = False }

withKFlag :: Flag PragmaOptions
withKFlag o = return $ o { optWithoutK = False }

withoutKFlag :: Flag PragmaOptions
withoutKFlag o = return $ o { optWithoutK = True }

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

cubicalFlag :: Flag PragmaOptions
cubicalFlag o = return $ o { optCubical = True, optWithoutK = True }

postfixProjectionsFlag :: Flag PragmaOptions
postfixProjectionsFlag o = return $ o { optPostfixProjections = True }

instanceDepthFlag :: String -> Flag PragmaOptions
instanceDepthFlag s o = do
  d <- integerArgument "--instance-search-depth" s
  return $ o { optInstanceSearchDepth = d }

overlappingInstancesFlag :: Flag PragmaOptions
overlappingInstancesFlag o = return $ o { optOverlappingInstances = True }

noOverlappingInstancesFlag :: Flag PragmaOptions
noOverlappingInstancesFlag o = return $ o { optOverlappingInstances = False }

inversionMaxDepthFlag :: String -> Flag PragmaOptions
inversionMaxDepthFlag s o = do
  d <- integerArgument "--inversion-max-depth" s
  return $ o { optInversionMaxDepth = d }

interactiveFlag :: Flag CommandLineOptions
interactiveFlag  o = do
  prag <- allowUnsolvedFlag (optPragmaOptions o)
  return $ o { optInteractive    = True
             , optPragmaOptions = prag
             }

compileFlagNoMain :: Flag PragmaOptions
compileFlagNoMain o = return $ o { optCompileNoMain = True }

compileDirFlag :: FilePath -> Flag CommandLineOptions
compileDirFlag f o = return $ o { optCompileDir = Just f }

htmlFlag :: Flag CommandLineOptions
htmlFlag o = return $ o { optGenerateHTML = True }

htmlHighlightFlag :: String -> Flag CommandLineOptions
htmlHighlightFlag "code" o = return $ o { optHTMLHighlight = HighlightCode }
htmlHighlightFlag "all"  o = return $ o { optHTMLHighlight = HighlightAll  }
htmlHighlightFlag "auto" o = return $ o { optHTMLHighlight = HighlightAuto  }
htmlHighlightFlag opt    o = throwError $ "Invalid option <" ++ opt
  ++ ">, expected <all>, <auto> or <code>"

dependencyGraphFlag :: FilePath -> Flag CommandLineOptions
dependencyGraphFlag f o = return $ o { optDependencyGraph = Just f }

htmlDirFlag :: FilePath -> Flag CommandLineOptions
htmlDirFlag d o = return $ o { optHTMLDir = d }

cssFlag :: FilePath -> Flag CommandLineOptions
cssFlag f o = return $ o { optCSSFile = Just f }

includeFlag :: FilePath -> Flag CommandLineOptions
includeFlag d o = return $ o { optIncludePaths = d : optIncludePaths o }

libraryFlag :: String -> Flag CommandLineOptions
libraryFlag s o = return $ o { optLibraries = optLibraries o ++ [s] }

overrideLibrariesFileFlag :: String -> Flag CommandLineOptions
overrideLibrariesFileFlag s o = do
  ifM (liftIO $ doesFileExist s)
    {-then-} (return $ o { optOverrideLibrariesFile = Just s })
    {-else-} (throwError $ "Libraries file not found: " ++ s)

noDefaultLibsFlag :: Flag CommandLineOptions
noDefaultLibsFlag o = return $ o { optDefaultLibs = False }

noLibsFlag :: Flag CommandLineOptions
noLibsFlag o = return $ o { optUseLibs = False }

verboseFlag :: String -> Flag PragmaOptions
verboseFlag s o =
    do  (k,n) <- parseVerbose s
        return $ o { optVerbose = Trie.insert k n $ optVerbose o }
  where
    parseVerbose s = case wordsBy (`elem` (":." :: String)) s of
      []  -> usage
      ss  -> do
        n <- readM (last ss) `catchError` \_ -> usage
        return (init ss, n)
    usage = throwError "argument to verbose should be on the form x.y.z:N or N"

warningModeFlag :: String -> Flag PragmaOptions
warningModeFlag s o = case warningModeUpdate s of
  Just upd -> return $ o { optWarningMode = upd (optWarningMode o) }
  Nothing  -> throwError $ "unknown warning flag " ++ s ++ ". See --help=warning."

terminationDepthFlag :: String -> Flag PragmaOptions
terminationDepthFlag s o =
    do k <- readM s `catchError` \_ -> usage
       when (k < 1) $ usage -- or: turn termination checking off for 0
       return $ o { optTerminationDepth = CutOff $ k-1 }
    where usage = throwError "argument to termination-depth should be >= 1"

integerArgument :: String -> String -> OptM Int
integerArgument flag s =
    readM s `catchError` \_ ->
        throwError $ "option '" ++ flag ++ "' requires an integer argument"

standardOptions :: [OptDescr (Flag CommandLineOptions)]
standardOptions =
    [ Option ['V']  ["version"] (NoArg versionFlag)       "show version number"
    , Option ['?']  ["help"]    (OptArg helpFlag "TOPIC")
                      ("show help for TOPIC (available: "
                       ++ intercalate ", " (map fst allHelpTopics)
                       ++ ")")
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
    , Option []     ["latex"] (NoArg latexFlag)
                    "generate LaTeX with highlighted source code"
    , Option []     ["latex-dir"] (ReqArg latexDirFlag "DIR")
                    ("directory in which LaTeX files are placed (default: " ++
                     defaultLaTeXDir ++ ")")
    , Option []     ["html"] (NoArg htmlFlag)
                    "generate HTML files with highlighted source code"
    , Option []     ["html-dir"] (ReqArg htmlDirFlag "DIR")
                    ("directory in which HTML files are placed (default: " ++
                     defaultHTMLDir ++ ")")
    , Option []     ["css"] (ReqArg cssFlag "URL")
                    "the CSS file used by the HTML files (can be relative)"
    , Option []     ["html-highlight"] (ReqArg htmlHighlightFlag "[code,all,auto]")
                    ("whether to highlight only the code parts (code) or " ++
                    "the file as a whole (all) or " ++
                    "decide by source file type (auto)")
    , Option []     ["dependency-graph"] (ReqArg dependencyGraphFlag "FILE")
                    "generate a Dot file with a module dependency graph"
    , Option []     ["ignore-interfaces"] (NoArg ignoreInterfacesFlag)
                    "ignore interface files (re-type check everything)"
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
    , Option []     ["no-forcing"] (NoArg noForcingFlag)
                    "disable the forcing optimisation"
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
    ] ++ map (fmap lensPragmaOptions) deadPragmaOptions

pragmaOptions :: [OptDescr (Flag PragmaOptions)]
pragmaOptions =
    [ Option []     ["show-implicit"] (NoArg showImplicitFlag)
                    "show implicit arguments when printing"
    , Option []     ["show-irrelevant"] (NoArg showIrrelevantFlag)
                    "show irrelevant arguments when printing"
    , Option []     ["no-unicode"] (NoArg asciiOnlyFlag)
                    "don't use unicode characters when printing terms"
    , Option ['v']  ["verbose"] (ReqArg verboseFlag "N")
                    "set verbosity level to N"
    , Option []     ["allow-unsolved-metas"] (NoArg allowUnsolvedFlag)
                    "succeed and create interface file regardless of unsolved meta variables"
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
    , Option []     ["prop"] (NoArg propFlag)
                    "enable the use of the Prop universe"
    , Option []     ["no-prop"] (NoArg noPropFlag)
                    "disable the use of the Prop universe (default)"
    , Option []     ["sized-types"] (NoArg sizedTypes)
                    "enable sized types (default, inconsistent with --guardedness)"
    , Option []     ["no-sized-types"] (NoArg noSizedTypes)
                    "disable sized types"
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
    , Option []     ["rewriting"] (NoArg rewritingFlag)
                    "enable declaration and use of REWRITE rules"
    , Option []     ["cubical"] (NoArg cubicalFlag)
                    "enable cubical features (e.g. overloads lambdas for paths), implies --without-K"
    , Option []     ["postfix-projections"] (NoArg postfixProjectionsFlag)
                    "make postfix projection notation the default"
    , Option []     ["instance-search-depth"] (ReqArg instanceDepthFlag "N")
                    "set instance search depth to N (default: 500)"
    , Option []     ["overlapping-instances"] (NoArg overlappingInstancesFlag)
                    "consider recursive instance arguments during pruning of instance candidates"
    , Option []     ["no-overlapping-instances"] (NoArg noOverlappingInstancesFlag)
                    "don't consider recursive instance arguments during pruning of instance candidates (default)"
    , Option []     ["inversion-max-depth"] (ReqArg inversionMaxDepthFlag "N")
                    "set maximum depth for pattern match inversion to N (default: 50)"
    , Option []     ["safe"] (NoArg safeFlag)
                    "disable postulates, unsafe OPTION pragmas and primEraseEquality, implies --no-sized-types and --no-guardedness "
    , Option []     ["double-check"] (NoArg doubleCheckFlag)
                    "enable double-checking of all terms using the internal typechecker"
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
    , Option []     ["no-auto-inline"] (NoArg noAutoInlineFlag)
                    ("disable automatic compile-time inlining " ++
                     "(only definitions marked INLINE will be inlined)")
    , Option []     ["no-print-pattern-synonyms"] (NoArg noPrintPatSynFlag)
                    "expand pattern synonyms when printing terms"
    , Option []     ["no-fast-reduce"] (NoArg noFastReduceFlag)
                    "disable reduction using the Agda Abstract Machine"
    ]

-- | Pragma options of previous versions of Agda.
--   Should not be listed in the usage info, put parsed by GetOpt for good error messaging.
deadPragmaOptions :: [OptDescr (Flag PragmaOptions)]
deadPragmaOptions =
    [ Option []     ["guardedness-preserving-type-constructors"] (NoArg guardingTypeConstructorFlag)
                    "treat type constructors as inductive constructors when checking productivity"
    , Option []     ["no-coverage-check"] (NoArg dontCompletenessCheckFlag)
                    "the option has been removed"
    ]

-- | Used for printing usage info.
--   Does not include the dead options.
standardOptions_ :: [OptDescr ()]
standardOptions_ = map (fmap $ const ()) standardOptions

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
      longopts = map ("--" ++) $ concat $ map (\ (Option _ long _ _) -> long) opts

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
      sugs as  = "any of " ++ intercalate " " as

-- | Parse the standard options.
parseStandardOptions :: [String] -> OptM CommandLineOptions
parseStandardOptions argv = parseStandardOptions' argv defaultOptions

parseStandardOptions' :: [String] -> Flag CommandLineOptions
parseStandardOptions' argv opts = do
  opts <- getOptSimple (stripRTS argv) (deadStandardOptions ++ standardOptions) inputFlag opts
  checkOpts opts

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

-- Remove +RTS .. -RTS from arguments
stripRTS :: [String] -> [String]
stripRTS [] = []
stripRTS ("--RTS" : argv) = argv
stripRTS (arg : argv)
  | is "+RTS" arg = stripRTS $ drop 1 $ dropWhile (not . is "-RTS") argv
  | otherwise     = arg : stripRTS argv
  where
    is x arg = [x] == take 1 (words arg)

------------------------------------------------------------------------
-- Some paths

-- | Returns the absolute default lib dir. This directory is used to
-- store the Primitive.agda file.
defaultLibDir :: IO FilePath
defaultLibDir = do
  libdir <- fmap filePath (absolute =<< getDataFileName "lib")
  ifM (doesDirectoryExist libdir)
      (return libdir)
      (error $ "The lib directory " ++ libdir ++ " does not exist")
