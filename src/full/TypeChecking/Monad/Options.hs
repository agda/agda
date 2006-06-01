{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Options where

import Control.Monad.State
import Data.Maybe

import TypeChecking.Monad.Base
import Interaction.Options
import Utils.Monad

#include "../../undefined.h"

setCommandLineOptions :: CommandLineOptions -> TCM ()
setCommandLineOptions opts =
    modify $ \s -> s { stOptions = opts }

commandLineOptions :: TCM CommandLineOptions
commandLineOptions = gets stOptions

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

