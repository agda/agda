{-# OPTIONS -fglasgow-exts #-}

{-| Agda 2 main module.
-}
module Main where

import Control.Monad.State

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
import Syntax.Abstract.Test
import Syntax.Abstract.Name

import Interaction.Exceptions
import Interaction.CommandLine.CommandLine
import Interaction.Options
import Interaction.Monad

import TypeChecker
import TypeChecking.Monad
import TypeChecking.Monad.Context
import TypeChecking.Monad.Options
import TypeChecking.Reduce

import Utils.Monad

import Version

parseFile' :: Parser a -> FilePath -> IO a
parseFile' p file
    | "lagda" `isSuffixOf` file	= parseLiterateFile p file
    | otherwise			= parseFile p file


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
		when i $ liftIO $ putStr splashScreen
		let interaction | i	    = interactionLoop
				| otherwise = id
		interaction $ liftTCM $
		    do	hasFile <- hasInputFile
			resetState
			when hasFile $
			    do	file <- getInputFile
				(m, scope) <- liftIO $
				    do	m <- parseFile' moduleParser file
					concreteToAbstract_ m
				checkDecl m
				setScope scope

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
main =
    do	r <- runIM runAgda
	case r of
	    Left err -> do print err
			   exitFailure
	    Right () -> return ()

