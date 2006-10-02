{-# OPTIONS -fglasgow-exts #-}

{-| Agda 2 main module.
-}
module Main where

import Control.Monad.State
import Control.Monad.Error

import Data.List as List
import Data.Map as Map
import Data.Maybe

import System.Environment
import System.IO
import System.Exit

import Syntax.Parser
import Syntax.Concrete.Pretty ()
import qualified Syntax.Abstract as A
import Syntax.Translation.ConcreteToAbstract
import Syntax.Translation.AbstractToConcrete
import Syntax.Translation.InternalToAbstract
import Syntax.Abstract.Test
import Syntax.Abstract.Name
import Syntax.Strict

import Interaction.Exceptions
import Interaction.CommandLine.CommandLine
import Interaction.EmacsInterface.EmacsAgda
import Interaction.Options
import Interaction.Monad
import Interaction.GhciTop ()	-- to make sure it compiles

import TypeChecker
import TypeChecking.Monad
import TypeChecking.Reduce
import TypeChecking.Errors

import Compiler.Agate.TranslateName
import Compiler.Agate.OptimizedPrinter
import Compiler.Agate.UntypedPrinter

import Utils.Monad

import Version

-- | The main function
runAgda :: IM ()
runAgda =
    do	progName <- liftIO getProgName
	argv	 <- liftIO getArgs
	let opts = parseStandardOptions progName argv
	case opts of
	    Left err	-> liftIO $ optionError err
	    Right opts
		| optShowHelp opts	-> liftIO printUsage
		| optShowVersion opts	-> liftIO printVersion
		| isNothing (optInputFile opts)
		    && not (optInteractive opts)
		    && not (optEmacsMode opts)
					-> liftIO printUsage
		| otherwise		-> do setCommandLineOptions opts
					      checkFile
    where
	checkFile :: IM ()
	checkFile =
	    do	i <- optInteractive <$> liftTCM commandLineOptions
		emacs <- optEmacsMode <$> liftTCM commandLineOptions
		when i $ liftIO $ putStr splashScreen
		let interaction | i	    = interactionLoop
				| emacs	    = emacsModeLoop
				| otherwise = id
		interaction $ liftTCM $
		    do	hasFile <- hasInputFile
			resetState
			when hasFile $
			    do	file <- getInputFile
				(pragmas, m) <- liftIO $ parseFile' moduleParser file
				pragmas	     <- concreteToAbstract_ pragmas -- identity for top-level pragmas
				(m, scope)   <- concreteToAbstract_ m
				setOptionsFromPragmas pragmas
				checkDecl m
				setScope scope
				-- Print stats
				stats <- Map.toList <$> getStatistics
				case stats of
				    []	-> return ()
				    _	-> liftIO $ do
					putStrLn "Statistics"
					putStrLn "----------"
					mapM_ (\ (s,n) -> putStrLn $ s ++ " : " ++ show n) $
					    List.sortBy (\x y -> compare (snd x) (snd y)) stats


-- | Print usage information.
printUsage :: IO ()
printUsage =
    do	progName <- getProgName
	putStr $ usage standardOptions_ [] progName

-- | Print version information.
printVersion :: IO ()
printVersion =
    putStrLn $ "Agda 2 version " ++ version

-- | What to do for bad options.
optionError :: String -> IO ()
optionError err =
    do	putStr $ "Unrecognised argument: " ++ err
	printUsage
	exitFailure

-- | Main
main :: IO ()
main = do
    runIM $ runAgda `catchError` \err -> do
	s <- prettyError err
	liftIO $ putStrLn s
	liftIO $ exitFailure
    return ()

