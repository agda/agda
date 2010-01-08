{-# LANGUAGE CPP #-}

module Agda.Interaction.Options
    ( CommandLineOptions(..)
    , Flag
    , checkOpts
    , parseStandardOptions
    , parsePragmaOptions
    , parsePluginOptions
    , defaultOptions
    , standardOptions_
    , isLiterate
    , mapFlag
    , usage
    , tests
    ) where

import Control.Monad.Error	( MonadError(catchError) )
import Data.List		( isSuffixOf )
import System.Console.GetOpt	(getOpt, usageInfo, ArgOrder(ReturnInOrder)
				, OptDescr(..), ArgDescr(..)
				)
import Agda.Utils.TestHelpers   ( runTests )
import Agda.Utils.QuickCheck    ( quickCheck' )
import Agda.Utils.Monad		( readM )
import Agda.Utils.List               ( wordsBy )
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

data CommandLineOptions =
    Options { optProgramName          :: String
	    , optInputFile            :: Maybe FilePath
	    , optIncludeDirs          :: [FilePath]
	    , optShowVersion          :: Bool
	    , optShowHelp             :: Bool
	    , optInteractive          :: Bool
	    , optVerbose              :: Trie String Int
	    , optProofIrrelevance     :: Bool
	    , optAllowUnsolved        :: Bool
	    , optShowImplicit         :: Bool
	    , optRunTests             :: Bool
	    , optCompile              :: Bool
	    , optGenerateVimFile      :: Bool
	    , optGenerateHTML         :: Bool
	    , optHTMLDir              :: FilePath
	    , optCSSFile              :: Maybe FilePath
	    , optIgnoreInterfaces     :: Bool
	    , optDisablePositivity    :: Bool
	    , optCompileAlonzo        :: Bool
            , optCompileMAlonzo       :: Bool
            , optMAlonzoDir           :: Maybe FilePath
              -- ^ In the absence of a path the project root is used.
	    , optTerminationCheck     :: Bool
	    , optCompletenessCheck    :: Bool
            , optUnreachableCheck     :: Bool
	    , optUniverseCheck        :: Bool
            , optSizedTypes           :: Bool
            , optUniversePolymorphism :: Bool
            , optInjectiveTypeConstructors :: Bool
            , optGhcFlags             :: [String]
	    }
    deriving Show

-- | Map a function over the long options. Also removes the short options.
--   Will be used to add the plugin name to the plugin options.
mapFlag :: (String -> String) -> OptDescr a -> OptDescr a
mapFlag f (Option _ long arg descr) = Option [] (map f long) arg descr

defaultOptions :: CommandLineOptions
defaultOptions =
    Options { optProgramName          = "agda"
	    , optInputFile            = Nothing
	    , optIncludeDirs          = []
	    , optShowVersion          = False
	    , optShowHelp             = False
	    , optInteractive          = False
	    , optVerbose              = Trie.singleton [] 1
	    , optProofIrrelevance     = False
	    , optAllowUnsolved        = False
	    , optShowImplicit         = False
	    , optRunTests             = False
	    , optCompile              = False
	    , optGenerateVimFile      = False
	    , optGenerateHTML         = False
	    , optHTMLDir              = defaultHTMLDir
	    , optCSSFile              = Nothing
	    , optIgnoreInterfaces     = False
	    , optDisablePositivity    = False
	    , optCompileAlonzo        = False
	    , optCompileMAlonzo       = False
            , optMAlonzoDir           = Nothing
            , optTerminationCheck     = True
            , optCompletenessCheck    = True
            , optUnreachableCheck     = True
            , optUniverseCheck        = True
            , optSizedTypes           = False
            , optUniversePolymorphism = False
            , optInjectiveTypeConstructors = False
            , optGhcFlags             = []
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
type Flag opts	= opts -> Either String opts

-- | Checks that the given options are consistent.

checkOpts :: Flag CommandLineOptions
checkOpts opts
  | not (atMostOne compilerOpts) =
    Left "At most one compiler may be used.\n"
  | not (atMostOne $ optAllowUnsolved : compilerOpts) = Left
      "Unsolved meta variables are not allowed when compiling.\n"
  | not (atMostOne $ optInteractive : compilerOpts) =
      Left "Choose at most one: compiler or interactive mode.\n"
  | not (atMostOne [optGenerateHTML, optInteractive]) =
      Left "Choose at most one: HTML generator or interactive mode.\n"
  | not (atMostOne [optUniversePolymorphism, not . optUniverseCheck]) =
      Left "Cannot have both universe polymorphism and type in type.\n"
  | otherwise = Right opts
  where
  atMostOne bs = length (filter ($ opts) bs) <= 1

  compilerOpts =
    [ optCompile
    , optCompileAlonzo
    , optCompileMAlonzo
    ]

inputFlag :: FilePath -> CommandLineOptions -> Either String CommandLineOptions
inputFlag f o	    =
    case optInputFile o of
	Nothing  -> checkOpts $ o { optInputFile = Just f }
	Just _	 -> fail "only one input file allowed"

versionFlag               o = checkOpts $ o { optShowVersion          = True  }
helpFlag                  o = checkOpts $ o { optShowHelp             = True  }
proofIrrelevanceFlag      o = checkOpts $ o { optProofIrrelevance     = True  }
ignoreInterfacesFlag      o = checkOpts $ o { optIgnoreInterfaces     = True  }
allowUnsolvedFlag         o = checkOpts $ o { optAllowUnsolved        = True  }
showImplicitFlag          o = checkOpts $ o { optShowImplicit         = True  }
runTestsFlag              o = checkOpts $ o { optRunTests             = True  }
vimFlag                   o = checkOpts $ o { optGenerateVimFile      = True  }
noPositivityFlag          o = checkOpts $ o { optDisablePositivity    = True  }
dontTerminationCheckFlag  o = checkOpts $ o { optTerminationCheck     = False }
dontCompletenessCheckFlag o = checkOpts $ o { optCompletenessCheck    = False }
noUnreachableCheckFlag    o = checkOpts $ o { optUnreachableCheck     = False }
dontUniverseCheckFlag     o = checkOpts $ o { optUniverseCheck        = False }
sizedTypes                o = checkOpts $ o { optSizedTypes           = True  }
injectiveTypeConstructorFlag o = checkOpts $ o { optInjectiveTypeConstructors = True }
universePolymorphismFlag  o = checkOpts $ o { optUniversePolymorphism = True  }

interactiveFlag o = checkOpts $ o { optInteractive   = True
			          , optAllowUnsolved = True
			          }
compileFlag      o = checkOpts $ o { optCompileMAlonzo = True }
agateFlag        o = checkOpts $ o { optCompile        = True }
alonzoFlag       o = checkOpts $ o { optCompileAlonzo  = True }
malonzoFlag      o = checkOpts $ o { optCompileMAlonzo = True }
malonzoDirFlag f o = checkOpts $ o { optMAlonzoDir     = Just f }
ghcFlag        f o = checkOpts $ o { optGhcFlags       = f : optGhcFlags o }

htmlFlag      o = checkOpts $ o { optGenerateHTML = True }
htmlDirFlag d o = checkOpts $ o { optHTMLDir      = d }
cssFlag     f o = checkOpts $ o { optCSSFile      = Just f }

includeFlag d o	    = checkOpts $ o { optIncludeDirs   = d : optIncludeDirs o   }
verboseFlag s o	    =
    do	(k,n) <- parseVerbose s
	checkOpts $ o { optVerbose = Trie.insert k n $ optVerbose o }
  where
    parseVerbose s = case wordsBy (`elem` ":.") s of
      []  -> usage
      ss  -> do
        n <- readM (last ss) `catchError` \_ -> usage
        return (init ss, n)
    usage = fail "argument to verbose should be on the form x.y.z:N or N"

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
    ] ++ pragmaOptions

pragmaOptions :: [OptDescr (Flag CommandLineOptions)]
pragmaOptions =
    [ Option ['v']  ["verbose"]	(ReqArg verboseFlag "N")
		    "set verbosity level to N"
    , Option []	    ["show-implicit"] (NoArg showImplicitFlag)
		    "show implicit arguments when printing"
    -- , Option []	    ["proof-irrelevance"] (NoArg proofIrrelevanceFlag)
    --     	    "enable proof irrelevance (experimental feature)"
    , Option []	    ["allow-unsolved-metas"] (NoArg allowUnsolvedFlag)
		    "allow unsolved meta variables (only needed in batch mode)"
    , Option []	    ["no-positivity-check"] (NoArg noPositivityFlag)
		    "do not warn about not strictly positive data types"
    , Option []	    ["no-termination-check"] (NoArg dontTerminationCheckFlag)
		    "do not warn about possibly nonterminating code"
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
    , Option []     ["universe-polymorphism"] (NoArg universePolymorphismFlag)
                    "enable universe polymorphism (experimental feature)"
    ]

-- | Used for printing usage info.
standardOptions_ :: [OptDescr ()]
standardOptions_ = map (fmap $ const ()) standardOptions

-- | Don't export
parseOptions' ::
    String -> [String] -> opts ->
    [OptDescr (Flag opts)] -> (String -> Flag opts) -> Either String opts
parseOptions' progName argv defaults opts fileArg =
    case (getOpt (ReturnInOrder fileArg) opts argv) of
	(o,_,[])    -> foldl (>>=) (return defaults) o
	(_,_,errs)  -> fail $ concat errs

-- | Parse the standard options.
parseStandardOptions :: String -> [String] -> Either String CommandLineOptions
parseStandardOptions progName argv =
    parseOptions' progName argv defaultOptions standardOptions inputFlag

-- | Parse options from an options pragma.
parsePragmaOptions :: [String] -> CommandLineOptions -> Either String CommandLineOptions
parsePragmaOptions argv opts =
    parseOptions' progName argv opts pragmaOptions $
    \s _ -> fail $ "Bad option in pragma: " ++ s
    where
	progName = optProgramName opts

-- | Parse options for a plugin.
parsePluginOptions ::
    String -> [String] ->
    opts -> [OptDescr (Flag opts)] ->
    Either String opts
parsePluginOptions progName argv defaults opts =
    parseOptions'
	progName argv defaults opts
	(\s _ -> fail $ "Internal error: Flag " ++ s ++ " passed to a plugin")

-- | The usage info message. The argument is the program name (probably
--   agdaLight).
usage :: [OptDescr ()] -> [(String, String, [String], [OptDescr ()])] -> String -> String
usage options pluginInfos progName =
	usageInfo (header progName) options ++
	"\nPlugins:\n" ++
        indent (concatMap pluginMsg pluginInfos)

    where
	header progName = unlines [ "Agda"
				  , ""
				  , "Usage: " ++ progName ++ " [OPTIONS...] FILE"
				  ]

	indent = unlines . map ("  " ++) . lines

        pluginMsg (name, help, inherited, opts)
            | null opts && null inherited = optHeader
            | otherwise = usageInfo (optHeader ++
                                     "  Plugin-specific options:" ++
				     inheritedOptions inherited
				     ) opts
            where
		optHeader = "\n" ++ name ++ "-plugin:\n" ++ indent help
		inheritedOptions [] = ""
		inheritedOptions pls =
		    "\n    Inherits options from: " ++ unwords pls

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Interaction.Options"
  [ quickCheck' prop_defaultOptions
  ]
