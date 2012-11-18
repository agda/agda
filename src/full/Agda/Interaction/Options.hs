{-# LANGUAGE StandaloneDeriving, DeriveFunctor #-}

module Agda.Interaction.Options
    ( CommandLineOptions(..)
    , PragmaOptions(..)
    , OptionsPragma
    , Flag
    , Verbosity(..)
    , checkOpts
    , parseStandardOptions
    , parsePragmaOptions
    , parsePluginOptions
    , defaultOptions
    , defaultInteractionOptions
    , defaultVerbosity
    , standardOptions_
    , unsafePragmaOptions
    , isLiterate
    , mapFlag
    , usage
    , tests
    ) where

import Control.Monad            ( when )
import Control.Monad.Error	( MonadError(..) )
import Data.Maybe (isJust)
import Data.List		( isSuffixOf , intercalate )
import System.Console.GetOpt	(getOpt, usageInfo, ArgOrder(ReturnInOrder)
				, OptDescr(..), ArgDescr(..)
				)
import Agda.Utils.TestHelpers   ( runTests )
import Agda.Utils.QuickCheck    ( quickCheck' )
import Agda.Utils.FileName      ( AbsolutePath )
import Agda.Utils.Monad		( readM )
import Agda.Utils.List               ( wordsBy )
import Agda.Utils.String             ( indent )
import Agda.Utils.Trie               ( Trie )
import qualified Agda.Utils.Trie as Trie

-- | This should probably go somewhere else.
isLiterate :: FilePath -> Bool
isLiterate file = ".lagda" `isSuffixOf` file

-- OptDescr is a Functor --------------------------------------------------

deriving instance Functor OptDescr
deriving instance Functor ArgDescr

-- | Verbosity levels.
--   Separate cases for 0 and 1 are for optimization.
data Verbosity
  = ZeroVerbosity                      -- ^ Verbosity level 0: silence. (For interaction.)
  | BatchVerbosity                     -- ^ Verbosity level 1: imports, warnings etc. (For batch.)
  | CustomVerbosity (Trie String Int)  -- ^ Trie of verbosity levels.  (For debugging.)

-- | Translate verbosity level into verbosity trie.
trieVerbosity :: Verbosity -> Trie String Int
trieVerbosity v = case v of
  ZeroVerbosity     -> Trie.singleton [] 0
  BatchVerbosity    -> Trie.singleton [] 1
  CustomVerbosity t -> t

instance Show Verbosity where
  show = show . trieVerbosity

data CommandLineOptions =
    Options { optProgramName          :: String
            , optInputFile            :: Maybe FilePath
            , optIncludeDirs          :: Either [FilePath] [AbsolutePath]
              -- ^ 'Left' is used temporarily, before the paths have
              -- been made absolute. An empty 'Left' list is
              -- interpreted as @["."]@ (see
              -- 'Agda.TypeChecking.Monad.Options.makeIncludeDirsAbsolute').
            , optShowVersion          :: Bool
            , optShowHelp             :: Bool
            , optInteractive          :: Bool
            , optRunTests             :: Bool
            , optGHCiInteraction      :: Bool
            , optCompile              :: Bool
            , optEpicCompile          :: Bool
            , optJSCompile            :: Bool
            , optCompileDir           :: Maybe FilePath
              -- ^ In the absence of a path the project root is used.
	    , optGenerateVimFile      :: Bool
            , optGenerateLaTeX        :: Bool
	    , optGenerateHTML         :: Bool
	    , optDependencyGraph      :: Maybe FilePath
	    , optLaTeXDir             :: FilePath
	    , optHTMLDir              :: FilePath
	    , optCSSFile              :: Maybe FilePath
	    , optIgnoreInterfaces     :: Bool
            , optForcing              :: Bool
            , optGhcFlags             :: [String]
            , optPragmaOptions        :: PragmaOptions
            , optEpicFlags            :: [String]
            , optSafe                 :: Bool
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
  , optTerminationDepth          :: Int
  , optCompletenessCheck         :: Bool
  , optUniverseCheck             :: Bool
  , optSizedTypes                :: Bool
  , optInjectiveTypeConstructors :: Bool
  , optGuardingTypeConstructors  :: Bool
  , optUniversePolymorphism      :: Bool
  , optIrrelevantProjections     :: Bool
  , optExperimentalIrrelevance   :: Bool  -- ^ irrelevant levels, irrelevant data matching
  , optWithoutK                  :: Bool
  , optCopatterns                :: Bool  -- ^ definitions by copattern matching
  }
  deriving Show

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

-- | For batch usage.
defaultVerbosity :: Verbosity
defaultVerbosity = BatchVerbosity -- Trie.singleton [] 1

-- | For interactive usage, do not print any debug messages
--   by default.
defaultInteractionVerbosity :: Verbosity
defaultInteractionVerbosity = ZeroVerbosity -- Trie.singleton [] 0

defaultInteractionOptions :: PragmaOptions
defaultInteractionOptions = defaultPragmaOptions
  { optVerbose = defaultInteractionVerbosity }

defaultOptions :: CommandLineOptions
defaultOptions =
    Options { optProgramName          = "agda"
            , optInputFile            = Nothing
            , optIncludeDirs          = Left []
            , optShowVersion          = False
            , optShowHelp             = False
            , optInteractive          = False
            , optRunTests             = False
            , optGHCiInteraction      = False
            , optCompile              = False
            , optEpicCompile          = False
            , optJSCompile            = False
            , optCompileDir           = Nothing
	    , optGenerateVimFile      = False
            , optGenerateLaTeX        = False
	    , optGenerateHTML         = False
	    , optDependencyGraph      = Nothing
	    , optLaTeXDir             = defaultLaTeXDir
	    , optHTMLDir              = defaultHTMLDir
	    , optCSSFile              = Nothing
	    , optIgnoreInterfaces     = False
            , optForcing              = True
            , optGhcFlags             = []
            , optPragmaOptions        = defaultPragmaOptions
            , optEpicFlags            = []
            , optSafe                 = False
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
  , optTerminationDepth          = 0    -- this is the cutoff value
  , optCompletenessCheck         = True
  , optUniverseCheck             = True
  , optSizedTypes                = False
  , optInjectiveTypeConstructors = False
  , optGuardingTypeConstructors  = False
  , optUniversePolymorphism      = True
  , optWithoutK                  = False
  , optCopatterns                = False
  }

-- | The default output directory for LaTeX.

defaultLaTeXDir = "latex"

-- | The default output directory for HTML.

defaultHTMLDir = "html"

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
  | not (atMostOne [optAllowUnsolved . p, optCompile]) = Left
      "Unsolved meta variables are not allowed when compiling.\n"
  | not (atMostOne [optGHCiInteraction, isJust . optInputFile]) =
      Left "Choose at most one: input file or --interaction.\n"
  | not (atMostOne $ interactive ++ [optCompile, optEpicCompile, optJSCompile]) =
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
  | otherwise = Right opts
  where
  atMostOne bs = length (filter ($ opts) bs) <= 1

  p = optPragmaOptions

  interactive = [optInteractive, optGHCiInteraction]

-- Check for unsafe pramas. Gives a list of used unsafe flags.

unsafePragmaOptions :: PragmaOptions -> [String]
unsafePragmaOptions opts =
  [ "--allow-unsolved-metas"                     | optAllowUnsolved opts             ] ++
  [ "--no-positivity-check"                      | optDisablePositivity opts         ] ++
  [ "--no-termination-check"                     | not (optTerminationCheck opts)    ] ++
  [ "--no-coverage-check"                        | not (optCompletenessCheck opts)   ] ++
  [ "--type-in-type"                             | not (optUniverseCheck opts)       ] ++
  [ "--sized-types"                              | optSizedTypes opts                ] ++
  [ "--injective-type-constructors"              | optInjectiveTypeConstructors opts ] ++
  [ "--guardedness-preserving-type-constructors" | optGuardingTypeConstructors opts  ] ++
  [ "--experimental-irrelevance"                 | optExperimentalIrrelevance opts   ] ++
  [ "--copatterns"                               | optCopatterns opts   ]

-- The default pragma options should be considered safe

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

versionFlag                  o = return $ o { optShowVersion               = True  }
helpFlag                     o = return $ o { optShowHelp                  = True  }
safeFlag                     o = return $ o { optSafe                      = True  }
proofIrrelevanceFlag         o = return $ o { optProofIrrelevance          = True  }
experimentalIrrelevanceFlag  o = return $ o { optExperimentalIrrelevance   = True  }
noIrrelevantProjectionsFlag  o = return $ o { optIrrelevantProjections     = False }
ignoreInterfacesFlag         o = return $ o { optIgnoreInterfaces          = True  }
allowUnsolvedFlag            o = return $ o { optAllowUnsolved             = True  }
showImplicitFlag             o = return $ o { optShowImplicit              = True  }
showIrrelevantFlag           o = return $ o { optShowIrrelevant            = True  }
runTestsFlag                 o = return $ o { optRunTests                  = True  }
ghciInteractionFlag          o = return $ o { optGHCiInteraction           = True  }
vimFlag                      o = return $ o { optGenerateVimFile           = True  }
latexFlag                    o = return $ o { optGenerateLaTeX             = True  }
latexDirFlag               d o = return $ o { optLaTeXDir                  = d     }
noPositivityFlag             o = return $ o { optDisablePositivity         = True  }
dontTerminationCheckFlag     o = return $ o { optTerminationCheck          = False }
dontCompletenessCheckFlag    o = return $ o { optCompletenessCheck         = False }
dontUniverseCheckFlag        o = return $ o { optUniverseCheck             = False
                                            , optUniversePolymorphism      = False }
sizedTypes                   o = return $ o { optSizedTypes                = True  }
injectiveTypeConstructorFlag o = return $ o { optInjectiveTypeConstructors = True  }
guardingTypeConstructorFlag  o = return $ o { optGuardingTypeConstructors  = True  }
universePolymorphismFlag     o = return $ o { optUniversePolymorphism      = True  }
noUniversePolymorphismFlag   o = return $ o { optUniversePolymorphism      = False }
noForcingFlag                o = return $ o { optForcing                   = False }
withoutKFlag                 o = return $ o { optWithoutK                  = True  }
copatternsFlag               o = return $ o { optCopatterns                = True  }

interactiveFlag  o = return $ o { optInteractive    = True
                                , optPragmaOptions  = (optPragmaOptions o)
                                                        { optAllowUnsolved = True }
                                }
compileFlag      o = return $ o { optCompile    = True }
compileEpicFlag  o = return $ o { optEpicCompile = True}
compileJSFlag    o = return $ o { optJSCompile = True}
compileDirFlag f o = return $ o { optCompileDir = Just f }
ghcFlag        f o = return $ o { optGhcFlags   = f : optGhcFlags o }
epicFlagsFlag  s o = return $ o { optEpicFlags  = optEpicFlags o ++ [s]}

htmlFlag      o = return $ o { optGenerateHTML = True }
dependencyGraphFlag f o = return $ o { optDependencyGraph  = Just f }
htmlDirFlag d o = return $ o { optHTMLDir      = d }
cssFlag     f o = return $ o { optCSSFile      = Just f }

includeFlag d o = return $ o { optIncludeDirs = Left (d : ds) }
  where ds = either id (const []) $ optIncludeDirs o

verboseFlag s o =
    do  (k,n) <- parseVerbose s
        return $ o { optVerbose = CustomVerbosity $ Trie.insert k n $ trieVerbosity $ optVerbose o }
  where
    parseVerbose s = case wordsBy (`elem` ":.") s of
      []  -> usage
      ss  -> do
        n <- readM (last ss) `catchError` \_ -> usage
        return (init ss, n)
    usage = throwError "argument to verbose should be on the form x.y.z:N or N"

terminationDepthFlag s o =
    do k <- readM s `catchError` \_ -> usage
       when (k < 1) $ usage -- or: turn termination checking off for 0
       return $ o { optTerminationDepth = k-1 }
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
    , Option []     ["epic"] (NoArg compileEpicFlag) "compile program using the Epic backend"
    , Option []     ["js"] (NoArg compileJSFlag) "compile program using the JS backend"
    , Option []     ["compile-dir"] (ReqArg compileDirFlag "DIR")
		    ("directory for compiler output (default: the project root)")
    , Option []     ["ghc-flag"] (ReqArg ghcFlag "GHC-FLAG")
                    "give the flag GHC-FLAG to GHC when compiling using MAlonzo"
    , Option []     ["epic-flag"] (ReqArg epicFlagsFlag "EPIC-FLAG")
                    "give the flag EPIC-FLAG to Epic when compiling using Epic"
    , Option []	    ["test"] (NoArg runTestsFlag)
		    "run internal test suite"
    , Option []	    ["vim"] (NoArg vimFlag)
		    "generate Vim highlighting files"
    , Option []	    ["latex"] (NoArg latexFlag)
                    "generate LaTeX with highlighted source code"
    , Option []	    ["latex-dir"] (ReqArg latexDirFlag "DIR")
                    ("directory in which LaTeX files are placed (default: " ++
                     defaultLaTeXDir ++ ")")
    , Option []	    ["html"] (NoArg htmlFlag)
		    "generate HTML files with highlighted source code"
    , Option []	    ["dependency-graph"] (ReqArg dependencyGraphFlag "FILE")
		    "generate a Dot file with a module dependency graph"
    , Option []	    ["html-dir"] (ReqArg htmlDirFlag "DIR")
                    ("directory in which HTML files are placed (default: " ++
                     defaultHTMLDir ++ ")")
    , Option []	    ["css"] (ReqArg cssFlag "URL")
		    "the CSS file used by the HTML files (can be relative)"
    , Option []	    ["ignore-interfaces"] (NoArg ignoreInterfacesFlag)
		    "ignore interface files (re-type check everything)"
    , Option ['i']  ["include-path"] (ReqArg includeFlag "DIR")
		    "look for imports in DIR"
    , Option []     ["no-forcing"] (NoArg noForcingFlag)
                    "disable the forcing optimisation"
    , Option []     ["safe"] (NoArg safeFlag)
                    "disable postulates, unsafe OPTION pragmas and primTrustMe"
    ] ++ map (fmap lift) pragmaOptions
  where
  lift :: Flag PragmaOptions -> Flag CommandLineOptions
  lift f = \opts -> do
    ps <- f (optPragmaOptions opts)
    return (opts { optPragmaOptions = ps })

pragmaOptions :: [OptDescr (Flag PragmaOptions)]
pragmaOptions =
    [ Option []	    ["show-implicit"] (NoArg showImplicitFlag)
		    "show implicit arguments when printing"
    , Option []	    ["show-irrelevant"] (NoArg showIrrelevantFlag)
		    "show irrelevant arguments when printing"
    , Option ['v']  ["verbose"]	(ReqArg verboseFlag "N")
                    "set verbosity level to N"
    -- , Option []	    ["proof-irrelevance"] (NoArg proofIrrelevanceFlag)
    --     	    "enable proof irrelevance (experimental feature)"
    , Option []	    ["allow-unsolved-metas"] (NoArg allowUnsolvedFlag)
		    "allow unsolved meta variables (only needed in batch mode)"
    , Option []	    ["no-positivity-check"] (NoArg noPositivityFlag)
		    "do not warn about not strictly positive data types"
    , Option []	    ["no-termination-check"] (NoArg dontTerminationCheckFlag)
		    "do not warn about possibly nonterminating code"
    , Option []	    ["termination-depth"] (ReqArg terminationDepthFlag "N")
		    "allow termination checker to count decrease/increase upto N (default N=1)"
    , Option []	    ["no-coverage-check"] (NoArg dontCompletenessCheckFlag)
		    "do not warn about possibly incomplete pattern matches"
    , Option []	    ["type-in-type"] (NoArg dontUniverseCheckFlag)
		    "ignore universe levels (this makes Agda inconsistent)"
    , Option []     ["sized-types"] (NoArg sizedTypes)
                    "use sized types (inconsistent with coinduction)"
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
    , Option []     ["without-K"] (NoArg withoutKFlag)
                    "disable the K rule (maybe)"
    , Option []     ["copatterns"] (NoArg copatternsFlag)
                    "enable definitions by copattern matching"
    ]

-- | Used for printing usage info.
standardOptions_ :: [OptDescr ()]
standardOptions_ = map (fmap $ const ()) standardOptions

-- | Don't export
parseOptions' ::
  [String] -> [OptDescr (Flag opts)] -> (String -> Flag opts) -> Flag opts
parseOptions' argv opts fileArg = \defaults ->
    case getOpt (ReturnInOrder fileArg) opts argv of
	(o,_,[])    -> foldl (>>=) (return defaults) o
	(_,_,errs)  -> throwError $ concat errs

-- | Parse the standard options.
parseStandardOptions :: [String] -> Either String CommandLineOptions
parseStandardOptions argv =
  checkOpts =<<
    parseOptions' argv standardOptions inputFlag defaultOptions

-- | Parse options from an options pragma.
parsePragmaOptions
  :: [String]
     -- ^ Pragma options.
  -> CommandLineOptions
     -- ^ Command-line options which should be updated.
  -> Either String PragmaOptions
parsePragmaOptions argv opts = do
  ps <- parseOptions' argv pragmaOptions
          (\s _ -> throwError $ "Bad option in pragma: " ++ s)
          (optPragmaOptions opts)
  checkOpts (opts { optPragmaOptions = ps })
  return ps

-- | Parse options for a plugin.
parsePluginOptions :: [String] -> [OptDescr (Flag opts)] -> Flag opts
parsePluginOptions argv opts =
  parseOptions' argv opts
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
-- All tests

tests :: IO Bool
tests = runTests "Agda.Interaction.Options"
  [ quickCheck' prop_defaultOptions
  , defaultPragmaOptionsSafe
  ]
