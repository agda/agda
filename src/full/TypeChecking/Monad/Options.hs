{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Options where

import Control.Monad.State
import Data.Maybe

import TypeChecking.Monad.Base
import Interaction.Options
import Utils.Monad
import Syntax.Abstract

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

