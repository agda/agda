{-# LANGUAGE CPP #-}

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
import qualified Agda.Utils.IO.Locale as LocIO
import System.Time

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
import Agda.Interaction.GhciTop ()      -- to make sure it compiles
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
                            -> liftIO printUsage
      | otherwise           -> do
          setCommandLineOptions opts
          checkFile
  where
    checkFile :: TCM ()
    checkFile = do
      i       <- optInteractive    <$> liftTCM commandLineOptions
      compile <- optCompile        <$> liftTCM commandLineOptions
      alonzo  <- optCompileAlonzo  <$> liftTCM commandLineOptions
      malonzo <- optCompileMAlonzo <$> liftTCM commandLineOptions
      when i $ liftIO $ LocIO.putStr splashScreen
      let failIfNoInt (Just i) = return i
          -- The allowed combinations of command-line
          -- options should rule out Nothing here.
          failIfNoInt Nothing  = __IMPOSSIBLE__

          interaction :: TCM (Maybe Interface) -> TCM ()
          interaction | i         = runIM . interactionLoop
                      | compile   = Agate.compilerMain         . (() <$)
                      | alonzo    = Alonzo.compilerMain        . (() <$)
                      | malonzo   = (MAlonzo.compilerMain =<<) . (failIfNoInt =<<)
                      | otherwise = (() <$)
      interaction $ do
        hasFile <- hasInputFile
        resetState
        if not hasFile then return Nothing else do
          file    <- getInputFile
          (i, mw) <- Imp.typeCheck file

          unsolvedOK <- optAllowUnsolved <$> pragmaOptions

          result <- case mw of
            Just (Imp.Warnings [] [] []) -> __IMPOSSIBLE__
            Just (Imp.Warnings _ unsolved@(_:_) _)
              | not unsolvedOK -> typeError $ UnsolvedMetas unsolved
            Just (Imp.Warnings _ _ unsolved@(_:_))
              | not unsolvedOK -> typeError $ UnsolvedConstraints unsolved
            Just (Imp.Warnings termErrs@(_:_) _ _) ->
              typeError $ TerminationCheckFailed termErrs
            Just _  -> return Nothing
            Nothing -> return $ Just i

          -- Print stats
          stats <- Map.toList <$> getStatistics
          case stats of
            []      -> return ()
            _       -> liftIO $ do
              LocIO.putStrLn "Statistics"
              LocIO.putStrLn "----------"
              mapM_ (\ (s,n) -> LocIO.putStrLn $ s ++ " : " ++ show n) $
                sortBy (\x y -> compare (snd x) (snd y)) stats

          whenM (optGenerateHTML <$> commandLineOptions) $ do
            case mw of
              Nothing -> generateHTML $ iModuleName i
              Just _  -> reportSLn "" 1
                "HTML is not generated (unsolved meta-variables)."

          return result

-- | Print usage information.
printUsage :: IO ()
printUsage = do
  progName <- getProgName
  LocIO.putStr $ usage standardOptions_ [] progName

-- | Print version information.
printVersion :: IO ()
printVersion =
  LocIO.putStrLn $ "Agda version " ++ version

-- | What to do for bad options.
optionError :: String -> IO ()
optionError err = do
  LocIO.putStrLn $ "Error: " ++ err
  printUsage
  exitFailure

-- | Main
main :: IO ()
main = do
    r <- runTCM $ runAgda `catchError` \err -> do
      s <- prettyError err
      liftIO $ LocIO.putStrLn s
      throwError err
    case r of
      Right _ -> exitSuccess
      Left _  -> exitFailure
  `catchImpossible` \e -> do
    LocIO.putStr $ show e
    exitFailure

