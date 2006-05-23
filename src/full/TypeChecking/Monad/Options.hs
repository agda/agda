{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Options where

import Control.Monad.State

import TypeChecking.Monad
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

getInputFile :: TCM FilePath
getInputFile =
    do	mf <- optInputFile <$> commandLineOptions
	case mf of
	    Just file	-> return file
	    Nothing	-> __IMPOSSIBLE__

