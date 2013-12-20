{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}

{-| Agda main module.
-}
module Agda.Main where

import Control.Monad.State
import Control.Monad.Error
import Control.Applicative

import Data.Maybe

import System.Environment
import System.Exit

import Agda.Syntax.Concrete.Pretty ()

import Agda.Interaction.CommandLine.CommandLine
import Agda.Interaction.Options
import Agda.Interaction.Monad
import Agda.Interaction.EmacsTop (mimicGHCi)
import Agda.Interaction.Imports (MaybeWarnings(..))
import qualified Agda.Interaction.Imports as Imp
import qualified Agda.Interaction.Highlighting.Dot as Dot
import qualified Agda.Interaction.Highlighting.LaTeX as LaTeX
import Agda.Interaction.Highlighting.HTML

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Errors

import Agda.Compiler.MAlonzo.Compiler as MAlonzo
import Agda.Compiler.Epic.Compiler as Epic
import Agda.Compiler.JS.Compiler as JS

import Agda.Utils.Monad

import Agda.Tests
import Agda.Version

#include "undefined.h"
import Agda.Utils.Impossible

-- | The main function
runAgda :: TCM ()
runAgda = do
  progName <- liftIO getProgName
  argv   <- liftIO getArgs
  let opts = parseStandardOptions argv
  case opts of
    Left err -> liftIO $ optionError err
    Right opts
      | optShowHelp opts    -> liftIO printUsage
      | optShowVersion opts -> liftIO printVersion
      | optRunTests opts    -> liftIO $ do
          ok <- testSuite
          unless ok exitFailure
      | isNothing (optInputFile opts)
          && not (optInteractive opts)
          && not (optGHCiInteraction opts)
                            -> liftIO printUsage
      | otherwise           -> do
          setCommandLineOptions opts
          checkFile
  where
    checkFile :: TCM ()
    checkFile = do
      i       <- optInteractive     <$> liftTCM commandLineOptions
      ghci    <- optGHCiInteraction <$> liftTCM commandLineOptions
      compile <- optCompile         <$> liftTCM commandLineOptions
      epic    <- optEpicCompile     <$> liftTCM commandLineOptions
      js      <- optJSCompile       <$> liftTCM commandLineOptions
      when i $ liftIO $ putStr splashScreen
      let failIfNoInt (Just i) = return i
          -- The allowed combinations of command-line
          -- options should rule out Nothing here.
          failIfNoInt Nothing  = __IMPOSSIBLE__

          failIfInt x Nothing  = x
          failIfInt _ (Just _) = __IMPOSSIBLE__

          interaction :: TCM (Maybe Interface) -> TCM ()
          interaction | i         = runIM . interactionLoop
                      | ghci      = (failIfInt mimicGHCi =<<)
                      | compile   = (MAlonzo.compilerMain =<<) . (failIfNoInt =<<)
                      | epic      = (Epic.compilerMain    =<<) . (failIfNoInt =<<)
                      | js        = (JS.compilerMain      =<<) . (failIfNoInt =<<)
                      | otherwise = (() <$)
      interaction $ do
        hasFile <- hasInputFile
        -- Andreas, 2013-10-30 The following 'resetState' kills the
        -- verbosity options.  That does not make sense (see fail/Issue641).
        -- 'resetState' here does not seem to serve any purpose,
        -- thus, I am removing it.
        -- resetState
        if not hasFile then return Nothing else do
          file    <- getInputFile
          (i, mw) <- Imp.typeCheckMain file

          unsolvedOK <- optAllowUnsolved <$> pragmaOptions

          result <- case mw of
            SomeWarnings (Warnings [] [] []) -> __IMPOSSIBLE__
            SomeWarnings (Warnings _ unsolved@(_:_) _)
              | not unsolvedOK -> typeError $ UnsolvedMetas unsolved
            SomeWarnings (Warnings _ _ unsolved@(_:_))
              | not unsolvedOK -> typeError $ UnsolvedConstraints unsolved
            SomeWarnings (Warnings termErrs@(_:_) _ _) ->
              typeError $ TerminationCheckFailed termErrs
            SomeWarnings _  -> return Nothing
            NoWarnings -> return $ Just i

          whenM (optGenerateHTML <$> commandLineOptions) $
            generateHTML $ iModuleName i

          whenM (isJust . optDependencyGraph <$> commandLineOptions) $
            Dot.generateDot $ i

          whenM (optGenerateLaTeX <$> commandLineOptions) $
            LaTeX.generateLaTeX (iModuleName i) (iHighlighting i)

          return result

-- | Print usage information.
printUsage :: IO ()
printUsage = do
  progName <- getProgName
  putStr $ usage standardOptions_ [] progName

-- | Print version information.
printVersion :: IO ()
printVersion =
  putStrLn $ "Agda version " ++ version

-- | What to do for bad options.
optionError :: String -> IO ()
optionError err = do
  putStrLn $ "Error: " ++ err
  printUsage
  exitFailure

-- | Main
main :: IO ()
main = do
    r <- runTCM $ runAgda `catchError` \err -> do
      s <- prettyError err
      liftIO $ putStrLn s
      throwError err
    case r of
      Right _ -> exitSuccess
      Left _  -> exitFailure
  `catchImpossible` \e -> do
    putStr $ show e
    exitFailure
