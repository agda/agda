{-# LANGUAGE CPP #-}

{-| Agda main module.
-}
module Agda.Main where

import Control.Monad.State
import Control.Applicative

import Data.Maybe

import System.Environment
import System.Exit

import Agda.Syntax.Position (Range)
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Abstract.Name (toTopLevelModuleName)

import Agda.Interaction.CommandLine
import Agda.Interaction.Options
import Agda.Interaction.Monad
import Agda.Interaction.EmacsTop (mimicGHCi)
import Agda.Interaction.Imports (MaybeWarnings'(..))
import qualified Agda.Interaction.Imports as Imp
import qualified Agda.Interaction.Highlighting.Dot as Dot
import qualified Agda.Interaction.Highlighting.LaTeX as LaTeX
import Agda.Interaction.Highlighting.HTML

import Agda.TypeChecking.Monad
import qualified Agda.TypeChecking.Monad.Benchmark as Bench
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Pretty

import Agda.Compiler.Common (IsMain (..))
import Agda.Compiler.MAlonzo.Compiler as MAlonzo
import Agda.Compiler.Epic.Compiler as Epic
import Agda.Compiler.JS.Compiler as JS
import Agda.Compiler.UHC.Compiler as UHC

import Agda.Utils.Lens
import Agda.Utils.Monad
import Agda.Utils.String

import Agda.Version

import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.Impossible

#include "undefined.h"

-- | The main function
runAgda :: TCM ()
runAgda = do
  progName <- liftIO getProgName
  argv     <- liftIO getArgs
  opts     <- liftIO $ runOptM $ parseStandardOptions argv
  case opts of
    Left err -> liftIO $ optionError err
    Right opts -> runAgdaWithOptions generateHTML progName opts

-- | Run Agda with parsed command line options and with a custom HTML generator
runAgdaWithOptions
  :: TCM ()             -- ^ HTML generating action
  -> String             -- ^ program name
  -> CommandLineOptions -- ^ parsed command line options
  -> TCM ()
runAgdaWithOptions generateHTML progName opts
      | optShowHelp opts    = liftIO printUsage
      | optShowVersion opts = liftIO printVersion
      | isNothing (optInputFile opts)
          && not (optInteractive opts)
          && not (optGHCiInteraction opts)
                            = liftIO printUsage
      | otherwise           = do
          -- Main function.
          -- Bill everything to root of Benchmark trie.
          Bench.billTo [] (checkFile opts) `finally_` do
            -- Print benchmarks.
            Bench.print

            -- Print accumulated statistics.
            printStatistics 20 Nothing =<< use lensAccumStatistics
  where
    checkFile :: CommandLineOptions -> TCM ()
    checkFile opts = do
      let i             = optInteractive     opts
          ghci          = optGHCiInteraction opts
          ghc           = optGhcCompile      opts
          compileNoMain = optCompileNoMain   opts
          epic          = optEpicCompile     opts
          js            = optJSCompile       opts
          uhc           = optUHCCompile      opts
      when i $ liftIO $ putStr splashScreen
      let failIfNoInt (Just i) = return i
          -- The allowed combinations of command-line
          -- options should rule out Nothing here.
          failIfNoInt Nothing  = __IMPOSSIBLE__

          failIfInt Nothing  = return ()
          failIfInt (Just _) = __IMPOSSIBLE__

          interaction :: TCM (Maybe Interface) -> TCM ()
          interaction | i             = runIM . interactionLoop
                      | ghci          = mimicGHCi . (failIfInt =<<)
                      | ghc && compileNoMain
                                      = (MAlonzo.compilerMain NotMain =<<) . (failIfNoInt =<<)
                      | ghc           = (MAlonzo.compilerMain IsMain =<<) . (failIfNoInt =<<)
                      | epic          = (Epic.compilerMain    =<<) . (failIfNoInt =<<)
                      | js            = (JS.compilerMain      =<<) . (failIfNoInt =<<)
                      | uhc && compileNoMain
                                      = (UHC.compilerMain NotMain =<<) . (failIfNoInt =<<)
                      | uhc           = (UHC.compilerMain IsMain =<<)  . (failIfNoInt =<<)
                      | otherwise     = (() <$)
      interaction $ do
        setCommandLineOptions opts
        hasFile <- hasInputFile
        -- Andreas, 2013-10-30 The following 'resetState' kills the
        -- verbosity options.  That does not make sense (see fail/Issue641).
        -- 'resetState' here does not seem to serve any purpose,
        -- thus, I am removing it.
        -- resetState
        if not hasFile then return Nothing else do
          file    <- getInputFile
          (i, mw) <- Imp.typeCheckMain file

          -- An interface is only generated if NoWarnings.
          result <- case mw of
            SomeWarnings ws -> do
              ws' <- applyFlagsToWarnings RespectFlags ws
              case ws' of
                []   -> return Nothing
                cuws -> warningsToError cuws
            NoWarnings      -> return $ Just i

          reportSDoc "main" 50 $ pretty i

          whenM (optGenerateHTML <$> commandLineOptions) $
            generateHTML

          whenM (isJust . optDependencyGraph <$> commandLineOptions) $
            Dot.generateDot $ i

          whenM (optGenerateLaTeX <$> commandLineOptions) $
            LaTeX.generateLaTeX (toTopLevelModuleName $ iModuleName i) (iHighlighting i)

          return result

-- | Print usage information.
printUsage :: IO ()
printUsage = do
  progName <- getProgName
  putStr $ usage standardOptions_ progName

-- | Print version information.
printVersion :: IO ()
printVersion =
  putStrLn $ "Agda version " ++ version

-- | What to do for bad options.
optionError :: String -> IO ()
optionError err = do
  putStrLn $ "Error: " ++ err ++ "\nRun 'agda --help' for help on command line options."
  exitFailure

-- | Run a TCM action in IO; catch and pretty print errors.
runTCMPrettyErrors :: TCM () -> IO ()
runTCMPrettyErrors tcm = do
    r <- runTCMTop $ tcm `catchError` \err -> do
      s <- prettyError err
      unless (null s) (liftIO $ putStrLn s)
      throwError err
    case r of
      Right _ -> exitSuccess
      Left _  -> exitFailure
  `catchImpossible` \e -> do
    putStr $ show e
    exitFailure

-- | Main
main :: IO ()
main = runTCMPrettyErrors runAgda
