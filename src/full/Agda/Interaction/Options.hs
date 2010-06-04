module Agda.Interaction.Options
    ( CommandLineOptions(..)
    , PragmaOptions(..)
    , OptionsPragma
    , Flag
    , Verbosity
    , checkOpts
    , parseStandardOptions
    , parsePragmaOptions
    , parsePluginOptions
    , defaultOptions
    , defaultVerbosity
    , standardOptions_
    , isLiterate
    , mapFlag
    , usage
    , tests
    ) where

import Control.Monad            ( when )
import Control.Monad.Error	( MonadError(catchError) )
import Data.List		( isSuffixOf )
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

instance Functor OptDescr where
    fmap f (Option short long arg descr) = Option short long (fmap f arg) descr

instance Functor ArgDescr where
    fmap f (NoArg x)	= NoArg (f x)
    fmap f (ReqArg p s) = ReqArg (f . p) s
    fmap f (OptArg p s) = OptArg (f . p) s

type Verbosity = Trie String Int

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
	    , optCompile              :: Bool
	    , optGenerateVimFile      :: Bool
	    , optGenerateHTML         :: Bool
	    , optHTMLDir              :: FilePath
	    , optCSSFile              :: Maybe FilePath
	    , optIgnoreInterfaces     :: Bool
	    , optCompileAlonzo        :: Bool
            , optCompileMAlonzo       :: Bool
            , optMAlonzoDir           :: Maybe FilePath
              -- ^ In the absence of a path the project root is used.
            , optGhcFlags             :: [String]
            , optPragmaOptions        :: PragmaOptions
	    }
    deriving Show

-- | Options which can be set in a pragma.

data PragmaOptions = PragmaOptions
  { optShowImplicit              :: Bool
  , optVerbose                   :: Verbosity
  , optProofIrrelevance          :: Bool
  , optAllowUnsolved             :: Bool
  , optDisablePositivity         :: Bool
  , optTerminationCheck          :: Bool
  , optTerminationDepth          :: Int
  , optCompletenessCheck         :: Bool
  , optUnreachableCheck          :: Bool
  , optUniverseCheck             :: Bool
  , optSizedTypes                :: Bool
  , optInjectiveTypeConstructors :: Bool
  , optGuardingTypeConstructors  :: Bool
  , optUniversePolymorphism      :: Bool
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

defaultVerbosity :: Verbosity
defaultVerbosity = Trie.singleton [] 1

defaultOptions :: CommandLineOptions
defaultOptions =
    Options { optProgramName          = "agda"
	    , optInputFile            = Nothing
	    , optIncludeDirs          = Left []
	    , optShowVersion          = False
	    , optShowHelp             = False
	    , optInteractive          = False
	    , optRunTests             = False
	    , optCompile              = False
	    , optGenerateVimFile      = False
	    , optGenerateHTML         = False
	    , optHTMLDir              = defaultHTMLDir
	    , optCSSFile              = Nothing
	    , optIgnoreInterfaces     = False
	    , optCompileAlonzo        = False
	    , optCompileMAlonzo       = False
            , optMAlonzoDir           = Nothing
            , optGhcFlags             = []
            , optPragmaOptions        = defaultPragmaOptions
	    }

defaultPragmaOptions :: PragmaOptions
defaultPragmaOptions = PragmaOptions
  { optShowImplicit              = False
  , optVerbose                   = defaultVerbosity
  , optProofIrrelevance          = False
  , optAllowUnsolved             = False
  , optDisablePositivity         = False
  , optTerminationCheck          = True
  , optTerminationDepth          = 0    -- this is the cutoff value
  , optCompletenessCheck         = True
  , optUnreachableCheck          = True
  , optUniverseCheck             = True
  , optSizedTypes                = False
  , optInjectiveTypeConstructors = False
  , optGuardingTypeConstructors  = False
  , optUniversePolymorphism      = False
  }

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
  | not (atMostOne compilerOpts) =
    Left "At most one compiler may be used.\n"
  | not (atMostOne $ optAllowUnsolved . p : compilerOpts) = Left
      "Unsolved meta variables are not allowed when compiling.\n"
  | not (atMostOne $ optInteractive : compilerOpts) =
      Left "Choose at most one: compiler or interactive mode.\n"
  | not (atMostOne [optGenerateHTML, optInteractive]) =
      Left "Choose at most one: HTML generator or interactive mode.\n"
  | not (atMostOne [ optUniversePolymorphism . p
                   , not . optUniverseCheck . p
                   ]) =
      Left "Cannot have both universe polymorphism and type in type.\n"
  | otherwise = Right opts
  where
  atMostOne bs = length (filter ($ opts) bs) <= 1

  p            = optPragmaOptions
  compilerOpts =
    [ optCompile
    , optCompileAlonzo
    , optCompileMAlonzo
    ]

inputFlag :: FilePath -> Flag CommandLineOptions
inputFlag f o =
    case optInputFile o of
	Nothing  -> return $ o { optInputFile = Just f }
	Just _	 -> fail "only one input file allowed"

versionFlag                  o = return $ o { optShowVersion               = True  }
helpFlag                     o = return $ o { optShowHelp                  = True  }
proofIrrelevanceFlag         o = return $ o { optProofIrrelevance          = True  }
ignoreInterfacesFlag         o = return $ o { optIgnoreInterfaces          = True  }
allowUnsolvedFlag            o = return $ o { optAllowUnsolved             = True  }
showImplicitFlag             o = return $ o { optShowImplicit              = True  }
runTestsFlag                 o = return $ o { optRunTests                  = True  }
vimFlag                      o = return $ o { optGenerateVimFile           = True  }
noPositivityFlag             o = return $ o { optDisablePositivity         = True  }
dontTerminationCheckFlag     o = return $ o { optTerminationCheck          = False }
dontCompletenessCheckFlag    o = return $ o { optCompletenessCheck         = False }
noUnreachableCheckFlag       o = return $ o { optUnreachableCheck          = False }
dontUniverseCheckFlag        o = return $ o { optUniverseCheck             = False }
sizedTypes                   o = return $ o { optSizedTypes                = True  }
injectiveTypeConstructorFlag o = return $ o { optInjectiveTypeConstructors = True  }
guardingTypeConstructorFlag  o = return $ o { optGuardingTypeConstructors  = True  }
universePolymorphismFlag     o = return $ o { optUniversePolymorphism      = True  }

interactiveFlag  o = return $ o { optInteractive    = True
                                , optPragmaOptions  = (optPragmaOptions o)
                                                        { optAllowUnsolved = True }
		                }
compileFlag      o = return $ o { optCompileMAlonzo = True }
agateFlag        o = return $ o { optCompile        = True }
alonzoFlag       o = return $ o { optCompileAlonzo  = True }
malonzoFlag      o = return $ o { optCompileMAlonzo = True }
malonzoDirFlag f o = return $ o { optMAlonzoDir     = Just f }
ghcFlag        f o = return $ o { optGhcFlags       = f : optGhcFlags o }

htmlFlag      o = return $ o { optGenerateHTML = True }
htmlDirFlag d o = return $ o { optHTMLDir      = d }
cssFlag     f o = return $ o { optCSSFile      = Just f }

includeFlag d o = return $ o { optIncludeDirs = Left (d : ds) }
  where ds = either id (const []) $ optIncludeDirs o

verboseFlag s o =
    do	(k,n) <- parseVerbose s
	return $ o { optVerbose = Trie.insert k n $ optVerbose o }
  where
    parseVerbose s = case wordsBy (`elem` ":.") s of
      []  -> usage
      ss  -> do
        n <- readM (last ss) `catchError` \_ -> usage
        return (init ss, n)
    usage = fail "argument to verbose should be on the form x.y.z:N or N"

terminationDepthFlag s o =
    do k <- readM s `catchError` \_ -> usage
       when (k < 1) $ usage -- or: turn termination checking off for 0
       return $ o { optTerminationDepth = k-1 }
    where usage = fail "argument to termination-depth should be >= 1"

integerArgument :: String -> String -> Either String Int
integerArgument flag s =
    readM s `catchError` \_ ->
	fail $ "option '" ++ flag ++ "' requires an integer argument"

standardOptions :: [OptDescr (Flag CommandLineOptions)]
standardOptions =
    [ Option ['V']  ["version"]	(NoArg versionFlag) "show version number"
    , Option ['?']  ["help"]	(NoArg helpFlag)    "show this help"
    , Option ['I']  ["interactive"] (NoArg interactiveFlag)
		    "start in interactive mode"
    , Option ['c']  ["compile"] (NoArg compileFlag)
                    "compile program (experimental)"
    , Option []     ["compile-dir"] (ReqArg malonzoDirFlag "DIR")
		    ("directory for compiler output (default: the project root)")
    , Option []     ["ghc-flag"] (ReqArg ghcFlag "GHC-FLAG")
                    "give the flag GHC-FLAG to GHC when compiling"
    , Option []	    ["test"] (NoArg runTestsFlag)
		    "run internal test suite"
    , Option []	    ["vim"] (NoArg vimFlag)
		    "generate Vim highlighting files"
    , Option []	    ["html"] (NoArg htmlFlag)
		    "generate HTML files with highlighted source code"
    , Option []	    ["html-dir"] (ReqArg htmlDirFlag "DIR")
                    ("directory in which HTML files are placed (default: " ++
                     defaultHTMLDir ++ ")")
    , Option []	    ["css"] (ReqArg cssFlag "URL")
		    "the CSS file used by the HTML files (can be relative)"
    , Option []	    ["ignore-interfaces"] (NoArg ignoreInterfacesFlag)
		    "ignore interface files (re-type check everything)"
    , Option ['i']  ["include-path"] (ReqArg includeFlag "DIR")
		    "look for imports in DIR"
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
    , Option []	    ["no-unreachable-check"] (NoArg noUnreachableCheckFlag)
		    "do not warn about unreachable function clauses"
    , Option []	    ["type-in-type"] (NoArg dontUniverseCheckFlag)
		    "ignore universe levels (this makes Agda inconsistent)"
    , Option []     ["sized-types"] (NoArg sizedTypes)
                    "use sized datatypes"
    , Option []     ["injective-type-constructors"] (NoArg injectiveTypeConstructorFlag)
                    "enable injective type constructors (makes Agda anti-classical and possibly inconsistent)"
    , Option []     ["guardedness-preserving-type-constructors"] (NoArg guardingTypeConstructorFlag)
                    "treat type constructors as inductive constructors when checking productivity"
    , Option []     ["universe-polymorphism"] (NoArg universePolymorphismFlag)
                    "enable universe polymorphism (experimental feature)"
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
	(_,_,errs)  -> fail $ concat errs

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
          (\s _ -> fail $ "Bad option in pragma: " ++ s)
          (optPragmaOptions opts)
  checkOpts (opts { optPragmaOptions = ps })
  return ps

-- | Parse options for a plugin.
parsePluginOptions :: [String] -> [OptDescr (Flag opts)] -> Flag opts
parsePluginOptions argv opts =
  parseOptions' argv opts
    (\s _ -> fail $ "Internal error: Flag " ++ s ++ " passed to a plugin")

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
				  , "Usage: " ++ progName ++ " [OPTIONS...] FILE"
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
  ]
