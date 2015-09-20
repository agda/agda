{-# LANGUAGE CPP #-}

module Agda.Interaction.Options
    ( CommandLineOptions(..)
    , PragmaOptions(..)
    , OptionsPragma
    , Flag
    , Verbosity
    , IncludeDirs
    , checkOpts
    , parseStandardOptions
    , parsePragmaOptions
    , parsePluginOptions
    , defaultOptions
    , defaultInteractionOptions
    , defaultVerbosity
    , defaultCutOff
    , standardOptions_
    , unsafePragmaOptions
    , isLiterate
    , mapFlag
    , usage
    , tests
    , defaultLibDir
    -- Reused by PandocAgda
    , inputFlag
    , standardOptions
    , getOptSimple
    ) where

import Control.Monad            ( when )

-- base-4.7 defines the Functor instances for OptDescr and ArgDescr
#if !(MIN_VERSION_base(4,7,0))
import Data.Orphans             ()
#endif

import Data.Maybe
import Data.List                ( isSuffixOf , intercalate )
import System.Console.GetOpt    ( getOpt', usageInfo, ArgOrder(ReturnInOrder)
                                , OptDescr(..), ArgDescr(..)
                                )
import System.Directory         ( doesDirectoryExist )

import Text.EditDistance

import Agda.Termination.CutOff  ( CutOff(..) )

import Agda.Utils.TestHelpers   ( runTests )
import Agda.Utils.QuickCheck    ( quickCheck' )
import Agda.Utils.FileName      ( absolute, AbsolutePath, filePath )
import Agda.Utils.Monad         ( ifM, readM )
import Agda.Utils.List          ( groupOn, wordsBy )
import Agda.Utils.String        ( indent )
import Agda.Utils.Trie          ( Trie )
import qualified Agda.Utils.Trie as Trie

import Agda.Utils.Except ( MonadError(catchError, throwError) )

-- Paths_Agda.hs is in $(BUILD_DIR)/build/autogen/.
import Paths_Agda ( getDataFileName )

-- | This should probably go somewhere else.
isLiterate :: FilePath -> Bool
isLiterate file = ".lagda" `isSuffixOf` file

-- OptDescr is a Functor --------------------------------------------------

type Verbosity = Trie String Int

type IncludeDirs = Either [FilePath] [AbsolutePath]
     -- ^ 'Left' is used temporarily, before the paths have
     -- been made absolute. An empty 'Left' list is
     -- interpreted as @["."]@ (see
     -- 'Agda.TypeChecking.Monad.Options.makeIncludeDirsAbsolute').

data CommandLineOptions = Options
  { optProgramName      :: String
  , optInputFile        :: Maybe FilePath
  , optIncludeDirs      :: IncludeDirs
  , optShowVersion      :: Bool
  , optShowHelp         :: Bool
  , optInteractive      :: Bool
  , optRunTests         :: Bool
  , optGHCiInteraction  :: Bool
  , optCompile          :: Bool
  , optCompileNoMain    :: Bool
  , optEpicCompile      :: Bool
  , optJSCompile        :: Bool
  , optUHCCompile       :: Bool
  , optUHCBin           :: Maybe FilePath
  , optUHCTextualCore   :: Bool
  , optUHCCallUHC       :: Bool
  , optUHCTraceLevel    :: Int
  , optOptimSmashing    :: Bool
  , optCompileDir       :: Maybe FilePath
  -- ^ In the absence of a path the project root is used.
  , optGenerateVimFile  :: Bool
  , optGenerateLaTeX    :: Bool
  , optGenerateHTML     :: Bool
  , optDependencyGraph  :: Maybe FilePath
  , optLaTeXDir         :: FilePath
  , optHTMLDir          :: FilePath
  , optCSSFile          :: Maybe FilePath
  , optIgnoreInterfaces :: Bool
  , optForcing          :: Bool
  , optGhcFlags         :: [String]
  , optPragmaOptions    :: PragmaOptions
  , optEpicFlags        :: [String]
  , optSafe             :: Bool
  , optSharing          :: Bool
  , optCaching          :: Bool
  }
  deriving Show

-- | Options which can be set in a pragma.

data PragmaOptions = PragmaOptions
  { optShowImplicit              :: Bool
  , optShowIrrelevant            :: Bool
  , optVerbose                   :: Verbosity
  , optProofIrrelevance          :: Bool
  , optAllowUnsolved             :: Bool
  , optDisablePositivity         :: Bool
  , optTerminationCheck          :: Bool
  , optTerminationDepth          :: CutOff
    -- ^ Cut off structural order comparison at some depth in termination checker?
  , optCompletenessCheck         :: Bool
  , optUniverseCheck             :: Bool
  , optSizedTypes                :: Bool
  , optInjectiveTypeConstructors :: Bool
  , optGuardingTypeConstructors  :: Bool
  , optUniversePolymorphism      :: Bool
  , optIrrelevantProjections     :: Bool
  , optExperimentalIrrelevance   :: Bool  -- ^ irrelevant levels, irrelevant data matching
  , optWithoutK                  :: Bool
  , optCopatterns                :: Bool  -- ^ Allow definitions by copattern matching?
  , optPatternMatching           :: Bool  -- ^ Is pattern matching allowed in the current file?
  , optExactSplit                :: Bool
  , optEta                       :: Bool
  , optRewriting                 :: Bool  -- ^ Can rewrite rules be added and used?
  }
  deriving (Show,Eq)

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
  , optIncludeDirs      = Left []
  , optShowVersion      = False
  , optShowHelp         = False
  , optInteractive      = False
  , optRunTests         = False
  , optGHCiInteraction  = False
  , optCompile          = False
  , optCompileNoMain    = False
  , optEpicCompile      = False
  , optJSCompile        = False
  , optUHCCompile       = False
  , optUHCBin           = Nothing
  , optUHCTextualCore   = False
  , optUHCCallUHC       = True
  , optUHCTraceLevel    = 0
  , optOptimSmashing    = True
  , optCompileDir       = Nothing
  , optGenerateVimFile  = False
  , optGenerateLaTeX    = False
  , optGenerateHTML     = False
  , optDependencyGraph  = Nothing
  , optLaTeXDir         = defaultLaTeXDir
  , optHTMLDir          = defaultHTMLDir
  , optCSSFile          = Nothing
  , optIgnoreInterfaces = False
  , optForcing          = True
  , optGhcFlags         = []
  , optPragmaOptions    = defaultPragmaOptions
  , optEpicFlags        = []
  , optSafe             = False
  , optSharing          = False
  , optCaching          = False
  }

defaultPragmaOptions :: PragmaOptions
defaultPragmaOptions = PragmaOptions
  { optShowImplicit              = False
  , optShowIrrelevant            = False
  , optVerbose                   = defaultVerbosity
  , optProofIrrelevance          = False
  , optExperimentalIrrelevance   = False
  , optIrrelevantProjections     = True
  , optAllowUnsolved             = False
  , optDisablePositivity         = False
  , optTerminationCheck          = True
  , optTerminationDepth          = defaultCutOff
  , optCompletenessCheck         = True
  , optUniverseCheck             = True
  , optSizedTypes                = True
  , optInjectiveTypeConstructors = False
  , optGuardingTypeConstructors  = False
  , optUniversePolymorphism      = True
  , optWithoutK                  = False
  , optCopatterns                = True
  , optPatternMatching           = True
  , optExactSplit                = False
  , optEta                       = True
  , optRewriting                 = False
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

prop_defaultOptions :: Bool
prop_defaultOptions = case checkOpts defaultOptions of
  Left  _ -> False
  Right _ -> True

{- | @f :: Flag opts@  is an action on the option record that results from
     parsing an option.  @f opts@ produces either an error message or an
     updated options record
-}
type Flag opts = opts -> Either String opts

-- | Checks that the given options are consistent.

checkOpts :: Flag CommandLineOptions
checkOpts opts
  | not (atMostOne [optAllowUnsolved . p, \x -> optCompile x]) = Left
      "Unsolved meta variables are not allowed when compiling.\n"
  | optCompileNoMain opts && (not (optCompile opts || optUHCCompile opts)) = Left
      "--no-main only allowed in combination with --compile.\n"
  | not (atMostOne [optGHCiInteraction, isJust . optInputFile]) =
      Left "Choose at most one: input file or --interaction.\n"
  | not (atMostOne $ interactive ++ [\x -> optCompile x, optEpicCompile, optJSCompile]) =
      Left "Choose at most one: compilers/--interactive/--interaction.\n"
  | not (atMostOne $ interactive ++ [optGenerateHTML]) =
      Left "Choose at most one: --html/--interactive/--interaction.\n"
  | not (atMostOne $ interactive ++ [isJust . optDependencyGraph]) =
      Left "Choose at most one: --dependency-graph/--interactive/--interaction.\n"
  | not (atMostOne [ optUniversePolymorphism . p
                   , not . optUniverseCheck . p
                   ]) =
      Left "Cannot have both universe polymorphism and type in type.\n"
  | not (atMostOne $ interactive ++ [optGenerateLaTeX]) =
      Left "Choose at most one: --latex/--interactive/--interaction.\n"
  | (not . null . optEpicFlags $ opts)
      && not (optEpicCompile opts) =
      Left "Cannot set Epic flags without using the Epic backend.\n"
  | (isJust $ optUHCBin opts)
      && not (optUHCCompile opts) =
      Left "Cannot set uhc binary without using UHC backend.\n"
  | (optUHCTextualCore opts)
      && not (optUHCCompile opts) =
      Left "Cannot set --uhc-textual-core without using UHC backend.\n"
  | otherwise = Right opts
  where
  atMostOne bs = length (filter ($ opts) bs) <= 1

  p = optPragmaOptions

  interactive = [optInteractive, optGHCiInteraction]

-- | Check for unsafe pramas. Gives a list of used unsafe flags.

unsafePragmaOptions :: PragmaOptions -> [String]
unsafePragmaOptions opts =
  [ "--allow-unsolved-metas"                     | optAllowUnsolved opts             ] ++
  [ "--no-positivity-check"                      | optDisablePositivity opts         ] ++
  [ "--no-termination-check"                     | not (optTerminationCheck opts)    ] ++
  [ "--no-coverage-check"                        | not (optCompletenessCheck opts)   ] ++
  [ "--type-in-type"                             | not (optUniverseCheck opts)       ] ++
  -- [ "--sized-types"                              | optSizedTypes opts                ] ++
  [ "--injective-type-constructors"              | optInjectiveTypeConstructors opts ] ++
  [ "--guardedness-preserving-type-constructors" | optGuardingTypeConstructors opts  ] ++
  [ "--experimental-irrelevance"                 | optExperimentalIrrelevance opts   ] ++
  [ "--rewriting"                                | optRewriting opts                 ] ++
  []

-- | The default pragma options should be considered safe.

defaultPragmaOptionsSafe :: IO Bool
defaultPragmaOptionsSafe
    | null unsafe = return True
    | otherwise   = do putStrLn $ "Following pragmas are default but not safe: "
                                        ++ intercalate ", " unsafe
                       return False
  where unsafe = unsafePragmaOptions defaultPragmaOptions

inputFlag :: FilePath -> Flag CommandLineOptions
inputFlag f o =
    case optInputFile o of
        Nothing  -> return $ o { optInputFile = Just f }
        Just _   -> throwError "only one input file allowed"

versionFlag :: Flag CommandLineOptions
versionFlag o = return $ o { optShowVersion = True }

helpFlag :: Flag CommandLineOptions
helpFlag o = return $ o { optShowHelp = True }

safeFlag :: Flag CommandLineOptions
safeFlag o = return $ o { optSafe = True }

sharingFlag :: Bool -> Flag CommandLineOptions
sharingFlag b o = return $ o { optSharing = b }

cachingFlag :: Bool -> Flag CommandLineOptions
cachingFlag b o = return $ o { optCaching = b }

proofIrrelevanceFlag :: Flag PragmaOptions
proofIrrelevanceFlag o = return $ o { optProofIrrelevance = True }

experimentalIrrelevanceFlag :: Flag PragmaOptions
experimentalIrrelevanceFlag o = return $ o { optExperimentalIrrelevance = True }

noIrrelevantProjectionsFlag :: Flag PragmaOptions
noIrrelevantProjectionsFlag o = return $ o { optIrrelevantProjections = False }

ignoreInterfacesFlag :: Flag CommandLineOptions
ignoreInterfacesFlag o = return $ o { optIgnoreInterfaces = True }

allowUnsolvedFlag :: Flag PragmaOptions
allowUnsolvedFlag o = return $ o { optAllowUnsolved = True }

showImplicitFlag :: Flag PragmaOptions
showImplicitFlag o = return $ o { optShowImplicit = True }

showIrrelevantFlag :: Flag PragmaOptions
showIrrelevantFlag o = return $ o { optShowIrrelevant = True }

runTestsFlag :: Flag CommandLineOptions
runTestsFlag o = return $ o { optRunTests = True }

ghciInteractionFlag :: Flag CommandLineOptions
ghciInteractionFlag o = return $ o { optGHCiInteraction = True }

vimFlag :: Flag CommandLineOptions
vimFlag o = return $ o { optGenerateVimFile = True }

latexFlag :: Flag CommandLineOptions
latexFlag o = return $ o { optGenerateLaTeX = True }

latexDirFlag :: FilePath -> Flag CommandLineOptions
latexDirFlag d o = return $ o { optLaTeXDir = d }

noPositivityFlag :: Flag PragmaOptions
noPositivityFlag o = return $ o { optDisablePositivity = True }

dontTerminationCheckFlag :: Flag PragmaOptions
dontTerminationCheckFlag o = return $ o { optTerminationCheck = False }

dontCompletenessCheckFlag :: Flag PragmaOptions
dontCompletenessCheckFlag o = return $ o { optCompletenessCheck = False }

dontUniverseCheckFlag :: Flag PragmaOptions
dontUniverseCheckFlag o = return $ o { optUniverseCheck        = False
                                     , optUniversePolymorphism = False
                                     }
etaFlag :: Flag PragmaOptions
etaFlag o = return $ o { optEta = True }

noEtaFlag :: Flag PragmaOptions
noEtaFlag o = return $ o { optEta = False }

sizedTypes :: Flag PragmaOptions
sizedTypes o = return $ o { optSizedTypes = True }

noSizedTypes :: Flag PragmaOptions
noSizedTypes o = return $ o { optSizedTypes = False }

injectiveTypeConstructorFlag :: Flag PragmaOptions
injectiveTypeConstructorFlag o = return $ o { optInjectiveTypeConstructors = True }

guardingTypeConstructorFlag :: Flag PragmaOptions
guardingTypeConstructorFlag o = return $ o { optGuardingTypeConstructors = True }

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
exactSplitFlag o = return $ o { optExactSplit = True }

noExactSplitFlag :: Flag PragmaOptions
noExactSplitFlag o = return $ o { optExactSplit = False }

rewritingFlag :: Flag PragmaOptions
rewritingFlag o = return $ o { optRewriting = True }

interactiveFlag :: Flag CommandLineOptions
interactiveFlag  o = return $ o { optInteractive    = True
                                , optPragmaOptions  = (optPragmaOptions o)
                                                      { optAllowUnsolved = True }
                                }

compileFlag :: Flag CommandLineOptions
compileFlag o = return $ o { optCompile = True }

compileFlagNoMain :: Flag CommandLineOptions
compileFlagNoMain o = return $ o { optCompileNoMain = True }

-- The Epic backend has been removed. See Issue 1481.
compileEpicFlag :: Flag CommandLineOptions
-- compileEpicFlag o = return $ o { optEpicCompile = True}
compileEpicFlag o = throwError "the Epic backend has been disabled"

compileJSFlag :: Flag CommandLineOptions
compileJSFlag  o = return $ o { optJSCompile = True }

compileUHCFlag :: Flag CommandLineOptions
compileUHCFlag o = return $ o { optUHCCompile = True}

compileDirFlag :: FilePath -> Flag CommandLineOptions
compileDirFlag f o = return $ o { optCompileDir = Just f }

-- NOTE: Quadratic in number of flags.
ghcFlag :: String -> Flag CommandLineOptions
ghcFlag f o = return $ o { optGhcFlags = optGhcFlags o ++ [f] }

-- NOTE: Quadratic in number of flags.
-- The Epic backend has been removed. See Issue 1481.
epicFlagsFlag :: String -> Flag CommandLineOptions
-- epicFlagsFlag s o = return $ o { optEpicFlags = optEpicFlags o ++ [s] }
epicFlagsFlag s o = throwError "the Epic backend has been disabled"

uhcBinFlag :: String -> Flag CommandLineOptions
uhcBinFlag s o = return $ o { optUHCBin  = Just s }

uhcTextualCoreFlag :: Flag CommandLineOptions
uhcTextualCoreFlag o = return $ o { optUHCTextualCore = True }

uhcCallUHCFlag :: Flag CommandLineOptions
uhcCallUHCFlag o = return $ o { optUHCCallUHC = False }

uhcTraceLevelFlag :: String -> Flag CommandLineOptions
-- TODO proper parsing and error handling
uhcTraceLevelFlag i o = return $ o { optUHCTraceLevel = read i }

optimNoSmashing :: Flag CommandLineOptions
optimNoSmashing o = return $ o {optOptimSmashing = False }

htmlFlag :: Flag CommandLineOptions
htmlFlag o = return $ o { optGenerateHTML = True }

dependencyGraphFlag :: FilePath -> Flag CommandLineOptions
dependencyGraphFlag f o = return $ o { optDependencyGraph = Just f }

htmlDirFlag :: FilePath -> Flag CommandLineOptions
htmlDirFlag d o = return $ o { optHTMLDir = d }

cssFlag :: FilePath -> Flag CommandLineOptions
cssFlag f o = return $ o { optCSSFile = Just f }

includeFlag :: FilePath -> Flag CommandLineOptions
includeFlag d o = return $ o { optIncludeDirs = Left (d : ds) }
  where ds = either id (const []) $ optIncludeDirs o

verboseFlag :: String -> Flag PragmaOptions
verboseFlag s o =
    do  (k,n) <- parseVerbose s
        return $ o { optVerbose = Trie.insert k n $ optVerbose o }
  where
    parseVerbose s = case wordsBy (`elem` ":.") s of
      []  -> usage
      ss  -> do
        n <- readM (last ss) `catchError` \_ -> usage
        return (init ss, n)
    usage = throwError "argument to verbose should be on the form x.y.z:N or N"

terminationDepthFlag :: String -> Flag PragmaOptions
terminationDepthFlag s o =
    do k <- readM s `catchError` \_ -> usage
       when (k < 1) $ usage -- or: turn termination checking off for 0
       return $ o { optTerminationDepth = CutOff $ k-1 }
    where usage = throwError "argument to termination-depth should be >= 1"

integerArgument :: String -> String -> Either String Int
integerArgument flag s =
    readM s `catchError` \_ ->
        throwError $ "option '" ++ flag ++ "' requires an integer argument"

standardOptions :: [OptDescr (Flag CommandLineOptions)]
standardOptions =
    [ Option ['V']  ["version"] (NoArg versionFlag) "show version number"
    , Option ['?']  ["help"]    (NoArg helpFlag)    "show this help"
    , Option ['I']  ["interactive"] (NoArg interactiveFlag)
                    "start in interactive mode"
    , Option []     ["interaction"] (NoArg ghciInteractionFlag)
                    "for use with the Emacs mode"
    , Option ['c']  ["compile"] (NoArg compileFlag)
                    "compile program using the MAlonzo backend (experimental)"
    , Option []     ["no-main"] (NoArg compileFlagNoMain)
                    "when compiling using the MAlonzo or UHC backend (experimental), do not treat the requested module as the main module of a program"

    -- The Epic backend has been removed. See Issue 1481.
    , Option []     ["epic"] (NoArg compileEpicFlag)
    --                "compile program using the Epic backend"
                    "the Epic backend has been removed"

    , Option []     ["js"] (NoArg compileJSFlag) "compile program using the JS backend"
    , Option []     ["uhc"] (NoArg compileUHCFlag) "compile program using the UHC backend"
    , Option []     ["uhc-bin"] (ReqArg uhcBinFlag "UHC") "The uhc binary to use when compiling with the UHC backend."
    , Option []     ["uhc-textual-core"] (NoArg uhcTextualCoreFlag) "Use textual core as intermediate representation instead of binary core."
    , Option []     ["uhc-dont-call-uhc"] (NoArg uhcCallUHCFlag) "Don't call uhc, just write the UHC Core files."
    , Option []     ["uhc-gen-trace"] (ReqArg uhcTraceLevelFlag "TRACE") "Add tracing code to generated executable."
    , Option []     ["no-smashing"] (NoArg optimNoSmashing) "Don't apply the smashing optimization."
    , Option []     ["compile-dir"] (ReqArg compileDirFlag "DIR")
                    ("directory for compiler output (default: the project root)")
    , Option []     ["ghc-flag"] (ReqArg ghcFlag "GHC-FLAG")
                    "give the flag GHC-FLAG to GHC when compiling using MAlonzo"

    -- The Epic backend has been removed. See Issue 1481.
    , Option []     ["epic-flag"] (ReqArg epicFlagsFlag "EPIC-FLAG")
    --                "give the flag EPIC-FLAG to Epic when compiling using Epic"
                    "the Epic backend has been removed"

    , Option []     ["test"] (NoArg runTestsFlag)
                    "run internal test suite"
    , Option []     ["vim"] (NoArg vimFlag)
                    "generate Vim highlighting files"
    , Option []     ["latex"] (NoArg latexFlag)
                    "generate LaTeX with highlighted source code"
    , Option []     ["latex-dir"] (ReqArg latexDirFlag "DIR")
                    ("directory in which LaTeX files are placed (default: " ++
                     defaultLaTeXDir ++ ")")
    , Option []     ["html"] (NoArg htmlFlag)
                    "generate HTML files with highlighted source code"
    , Option []     ["dependency-graph"] (ReqArg dependencyGraphFlag "FILE")
                    "generate a Dot file with a module dependency graph"
    , Option []     ["html-dir"] (ReqArg htmlDirFlag "DIR")
                    ("directory in which HTML files are placed (default: " ++
                     defaultHTMLDir ++ ")")
    , Option []     ["css"] (ReqArg cssFlag "URL")
                    "the CSS file used by the HTML files (can be relative)"
    , Option []     ["ignore-interfaces"] (NoArg ignoreInterfacesFlag)
                    "ignore interface files (re-type check everything)"
    , Option ['i']  ["include-path"] (ReqArg includeFlag "DIR")
                    "look for imports in DIR"
    , Option []     ["no-forcing"] (NoArg noForcingFlag)
                    "disable the forcing optimisation"
    , Option []     ["safe"] (NoArg safeFlag)
                    "disable postulates, unsafe OPTION pragmas and primTrustMe"
    , Option []     ["sharing"] (NoArg $ sharingFlag True)
                    "enable sharing and call-by-need evaluation (experimental) (default: OFF)"
    , Option []     ["no-sharing"] (NoArg $ sharingFlag False)
                    "disable sharing and call-by-need evaluation"
    , Option []     ["caching"] (NoArg $ cachingFlag True)
                    "enable caching of typechecking (experimental) (default: OFF)"
    , Option []     ["no-caching"] (NoArg $ cachingFlag False)
                    "disable caching of typechecking"
    ] ++ map (fmap lift) pragmaOptions
  where
  lift :: Flag PragmaOptions -> Flag CommandLineOptions
  lift f = \opts -> do
    ps <- f (optPragmaOptions opts)
    return (opts { optPragmaOptions = ps })

pragmaOptions :: [OptDescr (Flag PragmaOptions)]
pragmaOptions =
    [ Option []     ["show-implicit"] (NoArg showImplicitFlag)
                    "show implicit arguments when printing"
    , Option []     ["show-irrelevant"] (NoArg showIrrelevantFlag)
                    "show irrelevant arguments when printing"
    , Option ['v']  ["verbose"] (ReqArg verboseFlag "N")
                    "set verbosity level to N"
    -- , Option []          ["proof-irrelevance"] (NoArg proofIrrelevanceFlag)
    --              "enable proof irrelevance (experimental feature)"
    , Option []     ["allow-unsolved-metas"] (NoArg allowUnsolvedFlag)
                    "allow unsolved meta variables (only needed in batch mode)"
    , Option []     ["no-positivity-check"] (NoArg noPositivityFlag)
                    "do not warn about not strictly positive data types"
    , Option []     ["no-termination-check"] (NoArg dontTerminationCheckFlag)
                    "do not warn about possibly nonterminating code"
    , Option []     ["termination-depth"] (ReqArg terminationDepthFlag "N")
                    "allow termination checker to count decrease/increase upto N (default N=1)"
    , Option []     ["no-coverage-check"] (NoArg dontCompletenessCheckFlag)
                    "do not warn about possibly incomplete pattern matches"
    , Option []     ["type-in-type"] (NoArg dontUniverseCheckFlag)
                    "ignore universe levels (this makes Agda inconsistent)"
    , Option []     ["sized-types"] (NoArg sizedTypes)
                    "use sized types (default, inconsistent with `musical' coinduction)"
    , Option []     ["no-sized-types"] (NoArg noSizedTypes)
                    "disable sized types"
    , Option []     ["injective-type-constructors"] (NoArg injectiveTypeConstructorFlag)
                    "enable injective type constructors (makes Agda anti-classical and possibly inconsistent)"
    , Option []     ["guardedness-preserving-type-constructors"] (NoArg guardingTypeConstructorFlag)
                    "treat type constructors as inductive constructors when checking productivity"
    , Option []     ["no-universe-polymorphism"] (NoArg noUniversePolymorphismFlag)
                    "disable universe polymorphism"
    , Option []     ["universe-polymorphism"] (NoArg universePolymorphismFlag)
                    "enable universe polymorphism (default)"
    , Option []     ["no-irrelevant-projections"] (NoArg noIrrelevantProjectionsFlag)
                    "disable projection of irrelevant record fields"
    , Option []     ["experimental-irrelevance"] (NoArg experimentalIrrelevanceFlag)
                    "enable potentially unsound irrelevance features (irrelevant levels, irrelevant data matching)"
    , Option []     ["with-K"] (NoArg withKFlag)
                    "enable the K rule in pattern matching"
    , Option []     ["without-K"] (NoArg withoutKFlag)
                    "disable the K rule in pattern matching"
    , Option []     ["copatterns"] (NoArg copatternsFlag)
                    "enable definitions by copattern matching (default)"
    , Option []     ["no-copatterns"] (NoArg noCopatternsFlag)
                    "disable definitions by copattern matching"
    , Option []     ["no-pattern-matching"] (NoArg noPatternMatchingFlag)
                    "disable pattern matching completely"
    , Option []     ["exact-split"] (NoArg exactSplitFlag)
                    "require all clauses in a definition by pattern matching to hold as definitional equalities (except those marked as CATCHALL)"
    , Option []     ["no-exact-split"] (NoArg noExactSplitFlag)
                    "do not require all clauses in a definition by pattern matching to hold as definitional equalities (ignore those marked as CATCHALL)"
    , Option []     ["no-eta-equality"] (NoArg noEtaFlag)
                    "disable eta rules for records"
    , Option []     ["rewriting"] (NoArg rewritingFlag)
                    "enable declaration and use of REWRITE rules"
    ]

-- | Used for printing usage info.
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
parseStandardOptions :: [String] -> Either String CommandLineOptions
parseStandardOptions argv =
  checkOpts =<<
    getOptSimple argv standardOptions inputFlag defaultOptions

-- | Parse options from an options pragma.
parsePragmaOptions
  :: [String]
     -- ^ Pragma options.
  -> CommandLineOptions
     -- ^ Command-line options which should be updated.
  -> Either String PragmaOptions
parsePragmaOptions argv opts = do
  ps <- getOptSimple argv pragmaOptions
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
usage :: [OptDescr ()] -> [(String, String, [String], [OptDescr ()])] -> String -> String
usage options pluginInfos progName =
        usageInfo (header progName) options ++
        "\nPlugins:\n" ++
        indent 2 (concatMap pluginMsg pluginInfos)

    where
        header progName = unlines [ "Agda"
                                  , ""
                                  , "Usage: " ++ progName ++ " [OPTIONS...] [FILE]"
                                  ]

        pluginMsg (name, help, inherited, opts)
            | null opts && null inherited = optHeader
            | otherwise = usageInfo (optHeader ++
                                     "  Plugin-specific options:" ++
                                     inheritedOptions inherited
                                     ) opts
            where
                optHeader = "\n" ++ name ++ "-plugin:\n" ++ indent 2 help
                inheritedOptions [] = ""
                inheritedOptions pls =
                    "\n    Inherits options from: " ++ unwords pls

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

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Interaction.Options"
  [ quickCheck' prop_defaultOptions
  , defaultPragmaOptionsSafe
  ]
