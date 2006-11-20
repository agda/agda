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

setCommandLineOptions :: CommandLineOptions -> TCM ()
setCommandLineOptions opts =
    modify $ \s -> s { stOptions = opts }

commandLineOptions :: TCM CommandLineOptions
commandLineOptions = gets stOptions

setOptionsFromPragma :: Pragma -> TCM ()
setOptionsFromPragma (OptionsPragma xs) = do
    opts <- commandLineOptions
    case parsePragmaOptions xs opts of
	Left err    -> typeError $ GenericError err
	Right opts' -> setCommandLineOptions opts'
setOptionsFromPragma _ = return ()

setOptionsFromPragmas :: [Pragma] -> TCM ()
setOptionsFromPragmas = foldr (>>) (return ()) . map setOptionsFromPragma

bracketOptions :: TCM a -> TCM a
bracketOptions m = do
    opts <- commandLineOptions
    x    <- m
    setCommandLineOptions opts
    return x

getIncludeDirs :: TCM [FilePath]
getIncludeDirs = addDot . optIncludeDirs <$> commandLineOptions
    where
	addDot [] = ["."]   -- if there are no include dirs we use .
	addDot is = is

setInputFile :: FilePath -> TCM ()
setInputFile file =
    do	opts <- commandLineOptions
	setCommandLineOptions $ opts { optInputFile = Just file }

-- | Should only be run if 'hasInputFile'.
getInputFile :: TCM FilePath
getInputFile =
    do	mf <- optInputFile <$> commandLineOptions
	case mf of
	    Just file	-> return file
	    Nothing	-> __IMPOSSIBLE__

hasInputFile :: TCM Bool
hasInputFile = isJust <$> optInputFile <$> commandLineOptions

proofIrrelevance :: TCM Bool
proofIrrelevance = optProofIrrelevance <$> commandLineOptions

showImplicitArguments :: TCM Bool
showImplicitArguments = optShowImplicit <$> commandLineOptions

ignoreInterfaces :: TCM Bool
ignoreInterfaces = optIgnoreInterfaces <$> commandLineOptions

getVerbosity :: TCM Int
getVerbosity = optVerbose <$> commandLineOptions

verbose :: Int -> TCM () -> TCM ()
verbose n action = do
    m <- getVerbosity
    when (n <= m) action

report :: Int -> String -> TCM ()
report n s = verbose n $ liftIO $ putStr s

reportLn :: Int -> String -> TCM ()
reportLn n s = verbose n $ liftIO $ putStrLn s

