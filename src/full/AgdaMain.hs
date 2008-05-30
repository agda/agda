{-# OPTIONS -fglasgow-exts #-}

{-| Agda 2 main module.
-}
module AgdaMain where

import Prelude hiding (putStrLn, putStr, print)

import Control.Monad.State
import Control.Monad.Error
import Control.Applicative

import Data.List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe

import System.Environment
import System.IO hiding (putStrLn, putStr, print, hPutStr)
import System.Exit

import Syntax.Position
import Syntax.Parser
import Syntax.Concrete.Pretty ()
import qualified Syntax.Abstract as A
import Syntax.Abstract.Pretty
import Syntax.Translation.ConcreteToAbstract
import Syntax.Translation.AbstractToConcrete
import Syntax.Translation.InternalToAbstract
import Syntax.Abstract.Name
import Syntax.Strict
import Syntax.Scope.Base

import Interaction.Exceptions
import Interaction.CommandLine.CommandLine
import Interaction.Options
import Interaction.Monad
import Interaction.GhciTop ()	-- to make sure it compiles
import Interaction.Highlighting.Vim   (generateVimFile)
import Interaction.Highlighting.Emacs (generateEmacsFile)
import Interaction.Imports

import TypeChecker
import TypeChecking.Monad
import TypeChecking.Reduce
import TypeChecking.Errors
import qualified TypeChecking.Serialise
import TypeChecking.SerialiseShare

import Compiler.Agate.Main as Agate
import Compiler.Alonzo.Main as Alonzo
import Compiler.MAlonzo.Compiler as MAlonzo

import Termination.TermCheck

import Utils.Monad
import Utils.IO
import Utils.FileName
import Utils.Pretty
import Utils.Impossible

import Tests
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
		| optRunTests opts	-> liftIO runTests
		| isNothing (optInputFile opts)
		    && not (optInteractive opts)
					-> liftIO printUsage
		| otherwise		-> do setCommandLineOptions opts
					      checkFile
    where
	checkFile :: IM ()
	checkFile =
	    do	i	<- optInteractive <$> liftTCM commandLineOptions
		compile <- optCompile <$> liftTCM commandLineOptions
		alonzo <- optCompileAlonzo <$> liftTCM commandLineOptions
                malonzo <- optCompileMAlonzo <$> liftTCM commandLineOptions
		when i $ liftIO $ putStr splashScreen
		let interaction | i	  = interactionLoop
				| compile = Agate.compilerMain .(>> return ())
				| alonzo  = Alonzo.compilerMain .(>> return ())
                                | malonzo = MAlonzo.compilerMain .(>> return())
				| otherwise = \m -> do
				    (_, err) <- m
				    maybe (return ()) typeError err
		interaction $ liftTCM $
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

				reportLn 50 $ "SCOPE " ++ show (insideScope topLevel)

				-- Generate Vim file
				whenM (optGenerateVimFile <$> commandLineOptions) $
				    withScope_ (insideScope topLevel) $ generateVimFile file

				-- Generate Emacs file
				whenM (optGenerateEmacsFile <$> commandLineOptions) $
			          withScope_ (insideScope topLevel) $
                                    generateEmacsFile file topLevel errs

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
					putStrLn "Statistics"
					putStrLn "----------"
					mapM_ (\ (s,n) -> putStrLn $ s ++ " : " ++ show n) $
					    sortBy (\x y -> compare (snd x) (snd y)) stats

				return (insideScope topLevel, batchError)
			  else return (emptyScopeInfo, Nothing)

		return ()

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
    r <- runIM $ runAgda `catchError` \err -> do
	s <- prettyError err
	liftIO $ putStrLn s
	throwError err
    case r of
	Right _	-> return ()
	Left _	-> exitFailure
  `catchImpossible` \e -> do
    putStr $ show e
    exitFailure

