{-# OPTIONS -cpp -fglasgow-exts #-}

module Interaction.Options
    ( CommandLineOptions(..)
    , Flag
    , parseStandardOptions
    , parsePragmaOptions
    , parsePluginOptions
    , defaultOptions
    , standardOptions_
    , isLiterate
    , mapFlag
    , usage
    ) where

import Prelude hiding (print, putStr, putStrLn)
import Utils.IO

import Control.Monad.Error	( MonadError(catchError) )
import Data.List		( isSuffixOf )
import System.Console.GetOpt	(getOpt, usageInfo, ArgOrder(ReturnInOrder)
				, OptDescr(..), ArgDescr(..)
				)
import Utils.Monad		( readM )
import Utils.FileName		( slash )
import Utils.List               ( wordsBy )
import Utils.Trie               ( Trie )
import qualified Utils.Trie as Trie

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
    Options { optProgramName	   :: String
	    , optInputFile	   :: Maybe FilePath
	    , optIncludeDirs	   :: [FilePath]
	    , optShowVersion	   :: Bool
	    , optShowHelp	   :: Bool
	    , optInteractive	   :: Bool
	    , optEmacsMode	   :: Bool
	    , optVerbose	   :: Trie String Int
	    , optProofIrrelevance  :: Bool
	    , optAllowUnsolved	   :: Bool
	    , optShowImplicit	   :: Bool
	    , optRunTests	   :: Bool
	    , optCompile	   :: Bool
	    , optGenerateVimFile   :: Bool
	    , optIgnoreInterfaces  :: Bool
	    , optDisablePositivity :: Bool
	    , optCompileAlonzo     :: Bool
	    }
    deriving Show

-- | Map a function over the long options. Also removes the short options.
--   Will be used to add the plugin name to the plugin options.
mapFlag :: (String -> String) -> OptDescr a -> OptDescr a
mapFlag f (Option _ long arg descr) = Option [] (map f long) arg descr

defaultOptions :: CommandLineOptions
defaultOptions =
    Options { optProgramName	   = "agda"
	    , optInputFile	   = Nothing
	    , optIncludeDirs	   = []
	    , optShowVersion	   = False
	    , optShowHelp	   = False
	    , optInteractive	   = False
	    , optEmacsMode	   = False
	    , optVerbose	   = Trie.singleton [] 1
	    , optProofIrrelevance  = False
	    , optAllowUnsolved	   = False
	    , optShowImplicit	   = False
	    , optRunTests	   = False
	    , optCompile	   = False
	    , optGenerateVimFile   = False
	    , optIgnoreInterfaces  = False
	    , optDisablePositivity = False
	    , optCompileAlonzo     = False
	    }

{- | @f :: Flag opts@  is an action on the option record that results from
     parsing an option.  @f opts@ produces either an error message or an
     updated options record
-}
type Flag opts	= opts -> Either String opts

inputFlag f o	    =
    case optInputFile o of
	Nothing  -> return $ o { optInputFile = Just f }
	Just _	 -> fail "only one input file allowed"

versionFlag	     o = return $ o { optShowVersion	   = True }
helpFlag	     o = return $ o { optShowHelp	   = True }
proofIrrelevanceFlag o = return $ o { optProofIrrelevance  = True }
ignoreInterfacesFlag o = return $ o { optIgnoreInterfaces  = True }
allowUnsolvedFlag    o = return $ o { optAllowUnsolved	   = True }
showImplicitFlag     o = return $ o { optShowImplicit	   = True }
runTestsFlag	     o = return $ o { optRunTests	   = True }
vimFlag		     o = return $ o { optGenerateVimFile   = True }
noPositivityFlag     o = return $ o { optDisablePositivity = True }

interactiveFlag o
    | optEmacsMode o = fail "cannot have both emacs mode and interactive mode"
    | otherwise	     = return $ o { optInteractive   = True
				  , optAllowUnsolved = True
				  }
emacsModeFlag o
    | optInteractive o = fail "cannot have both emacs mode and interactive mode"
    | otherwise	       = return $ o { optEmacsMode     = True
				    , optAllowUnsolved = True
				    }
compileFlag o = return $ o { optCompile = True } -- todo: check exclusion
alonzoFlag o = return $ o { optCompileAlonzo = True } 

includeFlag d o	    = return $ o { optIncludeDirs   = d : optIncludeDirs o   }
verboseFlag s o	    =
    do	(k,n) <- parseVerbose s
	return $ o { optVerbose = Trie.insert k n $ optVerbose o }
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
    , Option ['v']  ["verbose"]	(ReqArg verboseFlag "N")
		    "set verbosity level to N"
    , Option ['i']  ["include-path"] (ReqArg includeFlag "DIR")
		    "look for imports in DIR"
    , Option ['I']  ["interactive"] (NoArg interactiveFlag)
		    "start in interactive mode"
    , Option []	    ["emacs-mode"] (NoArg emacsModeFlag)
		    "start in emacs mode"
    , Option []	    ["show-implicit"] (NoArg showImplicitFlag)
		    "show implicit arguments when printing"
    , Option []	    ["compile"] (NoArg compileFlag)
		    "translate program into GHC (experimental)"
    , Option ['c']  ["alonzo"] (NoArg alonzoFlag)
		    "translate program with Alonzo into GHC (experimental)"
    , Option []	    ["test"] (NoArg runTestsFlag)
		    "run internal test suite"
    , Option []	    ["vim"] (NoArg vimFlag)
		    "generate Vim highlighting files"
    , Option []	    ["ignore-interfaces"] (NoArg ignoreInterfacesFlag)
		    "ignore interface files (re-type check everything)"
    ] ++ pragmaOptions

pragmaOptions :: [OptDescr (Flag CommandLineOptions)]
pragmaOptions =
    [ Option []	    ["proof-irrelevance"] (NoArg proofIrrelevanceFlag)
		    "enable proof irrelevance (experimental feature)"
    , Option []	    ["allow-unsolved-metas"] (NoArg allowUnsolvedFlag)
		    "allow unsolved meta variables (only needed in batch mode)"
    , Option []	    ["disable-positivity-check"] (NoArg noPositivityFlag)
		    "disable strict positivity check for datatypes"
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
	header progName = unlines [ "Agda 2"
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

