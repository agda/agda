{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Options where

import Prelude hiding (putStr, putStrLn)

import Control.Monad.State
import Data.Maybe

import TypeChecking.Monad.Base
import Interaction.Options
import Syntax.Abstract
import Utils.Monad
import Utils.IO

#include "../../undefined.h"

setCommandLineOptions :: MonadTCM tcm => CommandLineOptions -> tcm ()
setCommandLineOptions opts =
    liftTCM $ modify $ \s -> s { stOptions = opts }

commandLineOptions :: MonadTCM tcm => tcm CommandLineOptions
commandLineOptions = liftTCM $ gets stOptions

setOptionsFromPragma :: MonadTCM tcm => Pragma -> tcm ()
setOptionsFromPragma (OptionsPragma xs) = do
    opts <- commandLineOptions
    case parsePragmaOptions xs opts of
	Left err    -> typeError $ GenericError err
	Right opts' -> setCommandLineOptions opts'
setOptionsFromPragma _ = return ()

setOptionsFromPragmas :: MonadTCM tcm => [Pragma] -> tcm ()
setOptionsFromPragmas = foldr (>>) (return ()) . map setOptionsFromPragma

bracketOptions :: MonadTCM tcm => tcm a -> tcm a
bracketOptions m = do
    opts <- commandLineOptions
    x    <- m
    setCommandLineOptions opts
    return x

getIncludeDirs :: MonadTCM tcm => tcm [FilePath]
getIncludeDirs = addDot . optIncludeDirs <$> commandLineOptions
    where
	addDot [] = ["."]   -- if there are no include dirs we use .
	addDot is = is

setInputFile :: MonadTCM tcm => FilePath -> tcm ()
setInputFile file =
    do	opts <- commandLineOptions
	setCommandLineOptions $ opts { optInputFile = Just file }

-- | Should only be run if 'hasInputFile'.
getInputFile :: MonadTCM tcm => tcm FilePath
getInputFile =
    do	mf <- optInputFile <$> commandLineOptions
	case mf of
	    Just file	-> return file
	    Nothing	-> __IMPOSSIBLE__

hasInputFile :: MonadTCM tcm => tcm Bool
hasInputFile = isJust <$> optInputFile <$> commandLineOptions

proofIrrelevance :: MonadTCM tcm => tcm Bool
proofIrrelevance = optProofIrrelevance <$> commandLineOptions

showImplicitArguments :: MonadTCM tcm => tcm Bool
showImplicitArguments = optShowImplicit <$> commandLineOptions

ignoreInterfaces :: MonadTCM tcm => tcm Bool
ignoreInterfaces = optIgnoreInterfaces <$> commandLineOptions

positivityCheckEnabled :: MonadTCM tcm => tcm Bool
positivityCheckEnabled = not . optDisablePositivity <$> commandLineOptions

getVerbosity :: MonadTCM tcm => tcm Int
getVerbosity = optVerbose <$> commandLineOptions

verbose :: MonadTCM tcm => Int -> tcm () -> tcm ()
verbose n action = do
    m <- getVerbosity
    when (n <= m) action

report :: MonadTCM tcm => Int -> String -> tcm ()
report n s = verbose n $ liftIO $ putStr s

reportLn :: MonadTCM tcm => Int -> String -> tcm ()
reportLn n s = verbose n $ liftIO $ putStrLn s

