{-# LANGUAGE CPP #-}
{-# LANGUAGE PatternGuards #-}

{-| Agda main module.
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

import Agda.Syntax.Position
import Agda.Syntax.Parser
import Agda.Syntax.Concrete.Pretty ()
import qualified Agda.Syntax.Abstract as A
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Translation.AbstractToConcrete
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Scope.Base

import Agda.Interaction.Exceptions
import Agda.Interaction.CommandLine.CommandLine
import Agda.Interaction.Options
import Agda.Interaction.Monad
import Agda.Interaction.GhcTop (mimicGHCi)
import qualified Agda.Interaction.Imports as Imp
import qualified Agda.Interaction.Highlighting.Dot as Dot
import qualified Agda.Interaction.Highlighting.LaTeX as LaTeX
import Agda.Interaction.Highlighting.HTML

import Agda.TypeChecker
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Errors
import qualified Agda.TypeChecking.Serialise
import Agda.TypeChecking.Serialise
import Agda.TypeChecking.SizedTypes

import Agda.Compiler.MAlonzo.Compiler as MAlonzo
import Agda.Compiler.Epic.Compiler as Epic
import Agda.Compiler.JS.Compiler as JS

import Agda.Termination.TermCheck

import Agda.Utils.Monad
import Agda.Utils.FileName
import Agda.Utils.Pretty

import Agda.Tests
import Agda.Version

import qualified System.IO as IO

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
        resetState
        if not hasFile then return Nothing else do
          file    <- getInputFile
          (i, mw) <- Imp.typeCheck file

          unsolvedOK <- optAllowUnsolved <$> pragmaOptions

          result <- case mw of
            Just (Warnings [] [] []) -> __IMPOSSIBLE__
            Just (Warnings _ unsolved@(_:_) _)
              | not unsolvedOK -> typeError $ UnsolvedMetas unsolved
            Just (Warnings _ _ unsolved@(_:_))
              | not unsolvedOK -> typeError $ UnsolvedConstraints unsolved
            Just (Warnings termErrs@(_:_) _ _) ->
              typeError $ TerminationCheckFailed termErrs
            Just _  -> return Nothing
            Nothing -> return $ Just i

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
