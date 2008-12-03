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
import qualified Agda.Interaction.Imports as Imp

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
	    Left err -> liftIO $ optionError err
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
		alonzo  <- optCompileAlonzo <$> liftTCM commandLineOptions
                malonzo <- optCompileMAlonzo <$> liftTCM commandLineOptions
		when i $ liftIO $ UTF8.putStr splashScreen
		let failIfError (_, Nothing)  = return ()
                    failIfError (_, Just err) = typeError err

                    interaction | i	  = runIM . interactionLoop
				| compile = Agate.compilerMain   . (failIfError =<<)
				| alonzo  = Alonzo.compilerMain  . (failIfError =<<)
                                | malonzo = MAlonzo.compilerMain . (failIfError =<<)
				| otherwise = \m -> do
				    (_, err) <- m
				    maybe (return ()) typeError err
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

                                let batchError = case ok of
                                      Imp.Warnings []             [] -> Nothing
                                      Imp.Warnings _  unsolved@(_:_)
                                        | unsolvedOK -> Nothing
                                        | otherwise  -> Just $ UnsolvedMetas unsolved
                                      Imp.Warnings termErrs@(_:_) _  ->
                                        Just (TerminationCheckFailed termErrs)
                                      Imp.Success {} -> Nothing

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

