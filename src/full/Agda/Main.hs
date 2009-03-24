{-# LANGUAGE CPP #-}

{-| Agda 2 main module.
-}
module Agda.Main where

import Control.Monad.State
import Control.Monad.Error
import Control.Applicative

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

import System.Environment
import System.Exit
import System.FilePath
import qualified System.IO.UTF8 as UTF8

import Agda.Syntax.Position
import Agda.Syntax.Parser
import Agda.Syntax.Concrete.Pretty ()
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Strict
import Agda.Syntax.Scope.Base

import Agda.Interaction.Exceptions
import Agda.Interaction.CommandLine.CommandLine
import Agda.Interaction.Options
import Agda.Interaction.Monad
import Agda.Interaction.GhciTop ()	-- to make sure it compiles
import qualified Agda.Interaction.Imports as Imp
import Agda.Interaction.Highlighting.HTML

import Agda.TypeChecker
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Errors
import qualified Agda.TypeChecking.Serialise
import Agda.TypeChecking.Serialise
import Agda.TypeChecking.SizedTypes

import Agda.Compiler.Agate.Main as Agate
import Agda.Compiler.Alonzo.Main as Alonzo
import Agda.Compiler.MAlonzo.Compiler as MAlonzo

import Agda.Termination.TermCheck

import Agda.Utils.Monad
import Agda.Utils.FileName
import Agda.Utils.Pretty

import Agda.Tests
import Agda.Version

import Paths_Agda (getDataDir)

#include "undefined.h"
import Agda.Utils.Impossible

-- | The main function
runAgda :: TCM ()
runAgda =
    do	progName <- liftIO getProgName
	argv	 <- liftIO getArgs
	let opts = parseStandardOptions progName argv
	case opts of
	    Left err -> liftIO $ optionError err
	    Right opts
		| optShowHelp opts	-> liftIO printUsage
		| optShowVersion opts	-> liftIO printVersion
                | optPrintEmacsDir opts -> liftIO printEmacsDir
		| optRunTests opts	-> liftIO $ do
                    ok <- testSuite
                    unless ok exitFailure
		| isNothing (optInputFile opts)
		    && not (optInteractive opts)
					-> liftIO printUsage
		| otherwise		-> do setCommandLineOptions opts
					      checkFile
    where
	checkFile :: TCM ()
	checkFile =
	    do	i	<- optInteractive <$> liftTCM commandLineOptions
		compile <- optCompile <$> liftTCM commandLineOptions
		alonzo  <- optCompileAlonzo <$> liftTCM commandLineOptions
                malonzo <- optCompileMAlonzo <$> liftTCM commandLineOptions
		when i $ liftIO $ UTF8.putStr splashScreen
		let failIfError (_, Right _)  = return ()
                    failIfError (_, Left err) = typeError err

                    failIfNoInt (_, Right (Just i)) = return i
                    -- The allowed combinations of command-line
                    -- options should rule out Right Nothing here.
                    failIfNoInt (_, Right Nothing)  = __IMPOSSIBLE__
                    failIfNoInt (_, Left err)       = typeError err

                    interaction | i	  = runIM . interactionLoop
				| compile = Agate.compilerMain   . (failIfError =<<)
				| alonzo  = Alonzo.compilerMain  . (failIfError =<<)
                                | malonzo = MAlonzo.compilerMain . (failIfNoInt =<<)
				| otherwise = (failIfError =<<)
		interaction $
		    do	hasFile <- hasInputFile
			resetState
			if hasFile then
			    do	file    <- getInputFile
                                options <- commandLineOptions

                                (topLevel, ok) <- Imp.createInterface options
                                  noTrace [] Map.empty
                                  Map.empty emptySignature
                                  Map.empty Nothing file False

                                -- The value of options from above
                                -- cannot be reused here, because then
                                -- options set in pragmas would have
                                -- no effect.
                                unsolvedOK <- optAllowUnsolved <$> commandLineOptions

                                let result = case ok of
                                      Imp.Warnings []             [] -> __IMPOSSIBLE__
                                      Imp.Warnings _  unsolved@(_:_)
                                        | unsolvedOK -> Right Nothing
                                        | otherwise  -> Left $ UnsolvedMetas unsolved
                                      Imp.Warnings termErrs@(_:_) _  ->
                                        Left (TerminationCheckFailed termErrs)
                                      Imp.Success { Imp.cirInterface = i } ->
                                        Right (Just i)

				-- Print stats
				stats <- Map.toList <$> getStatistics
				case stats of
				    []	-> return ()
				    _	-> liftIO $ do
					UTF8.putStrLn "Statistics"
					UTF8.putStrLn "----------"
					mapM_ (\ (s,n) -> UTF8.putStrLn $ s ++ " : " ++ show n) $
					    sortBy (\x y -> compare (snd x) (snd y)) stats

                                whenM (optGenerateHTML <$> commandLineOptions) $ do
                                  case ok of
                                    Imp.Success {} -> generateHTML $ topLevelModuleName topLevel
                                    _ -> return ()
                                         -- The error will be handled by interaction.

				return (insideScope topLevel, result)
			  else return (emptyScopeInfo, Right Nothing)

		return ()

-- | Print usage information.
printUsage :: IO ()
printUsage =
    do	progName <- getProgName
	UTF8.putStr $ usage standardOptions_ [] progName

-- | Print version information.
printVersion :: IO ()
printVersion =
    UTF8.putStrLn $ "Agda 2 version " ++ version

printEmacsDir :: IO ()
printEmacsDir = do
  dataDir <- getDataDir
  UTF8.putStr $ dataDir </> "emacs-mode"

-- | What to do for bad options.
optionError :: String -> IO ()
optionError err =
    do	UTF8.putStrLn $ "Error: " ++ err
	printUsage
	exitFailure

-- | Main
main :: IO ()
main = do
    r <- runTCM $ runAgda `catchError` \err -> do
	s <- prettyError err
	liftIO $ UTF8.putStrLn s
	throwError err
    case r of
	Right _	-> return ()
	Left _	-> exitFailure
  `catchImpossible` \e -> do
    UTF8.putStr $ show e
    exitFailure

