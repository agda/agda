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
import Agda.Interaction.Highlighting.Vim   (generateVimFile)
import Agda.Interaction.Highlighting.Emacs (generateEmacsFile)
import Agda.Interaction.Highlighting.Generate
  (TypeCheckingState(TypeCheckingDone))
import Agda.Interaction.Imports

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
import Agda.Utils.Impossible

import Agda.Tests
import Agda.Version

-- | The main function
runAgda :: TCM ()
runAgda =
    do	progName <- liftIO getProgName
	argv	 <- liftIO getArgs
	let opts = parseStandardOptions progName argv
	case opts of
	    Left err	-> liftIO $ optionError err
	    Right opts
		| optShowHelp opts	-> liftIO printUsage
		| optShowVersion opts	-> liftIO printVersion
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
		alonzo <- optCompileAlonzo <$> liftTCM commandLineOptions
                malonzo <- optCompileMAlonzo <$> liftTCM commandLineOptions
		when i $ liftIO $ UTF8.putStr splashScreen
		let interaction | i	  = runIM . interactionLoop
				| compile = Agate.compilerMain .(>> return ())
				| alonzo  = Alonzo.compilerMain .(>> return ())
                                | malonzo = MAlonzo.compilerMain .(>> return())
				| otherwise = \m -> do
				    (_, err) <- m
				    maybe (return ()) typeError err
		interaction $
		    do	hasFile <- hasInputFile
			resetState
			if hasFile then
			    do	file <- getInputFile

				-- Parse
				(pragmas, m) <- liftIO $ parseFile' moduleParser file

				-- Scope check
				pragmas  <- concat <$> concreteToAbstract_ pragmas -- identity for top-level pragmas
				topLevel <- concreteToAbstract_ (TopLevel m)
                                setOptionsFromPragmas pragmas

                                -- Check module name
                                checkModuleName topLevel file

				-- Type check
				checkDecls $ topLevelDecls topLevel

                                -- Termination check
                                errs <- ifM (optTerminationCheck <$> commandLineOptions)
                                            (termDecls $ topLevelDecls topLevel)
                                            (return [])
                                mapM_ (\e -> reportSLn "term.warn.no" 1
                                             (show (fst e) ++ " does NOT termination check")) errs

				let batchError | null errs = Nothing
					       | otherwise = Just TerminationCheckFailed

				-- Set the scope
				setScope $ outsideScope topLevel

				reportSLn "scope.top" 50 $ "SCOPE " ++ show (insideScope topLevel)

				-- Generate Vim file
				whenM (optGenerateVimFile <$> commandLineOptions) $
				    withScope_ (insideScope topLevel) $ generateVimFile file

				-- Generate Emacs file
				whenM (optGenerateEmacsFile <$> commandLineOptions) $
                                    generateEmacsFile file TypeCheckingDone topLevel errs

				-- Give error for unsolved metas
				unsolved <- getOpenMetas
				unlessM (optAllowUnsolved <$> commandLineOptions) $
				    unless (null unsolved) $
					typeError . UnsolvedMetas =<< mapM getMetaRange unsolved

				-- Generate interface file (only if no metas)
				when (null unsolved) $ do
				    i <- buildInterface
				    let ifile = setExtension ".agdai" file
				    liftIO $ encodeFile ifile i

				-- Print stats
				stats <- Map.toList <$> getStatistics
				case stats of
				    []	-> return ()
				    _	-> liftIO $ do
					UTF8.putStrLn "Statistics"
					UTF8.putStrLn "----------"
					mapM_ (\ (s,n) -> UTF8.putStrLn $ s ++ " : " ++ show n) $
					    sortBy (\x y -> compare (snd x) (snd y)) stats

				return (insideScope topLevel, batchError)
			  else return (emptyScopeInfo, Nothing)

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

-- | What to do for bad options.
optionError :: String -> IO ()
optionError err =
    do	UTF8.putStr $ "Unrecognised argument: " ++ err
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

