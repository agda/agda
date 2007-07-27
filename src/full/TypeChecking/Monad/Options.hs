{-# OPTIONS -cpp #-}

module TypeChecking.Monad.Options where

import Prelude hiding (putStr, putStrLn, print)

import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe
import Text.PrettyPrint

import TypeChecking.Monad.Base
import Interaction.Options
import Syntax.Abstract
import Utils.Monad
import Utils.IO
import Utils.List
import Utils.Trie (Trie)
import qualified Utils.Trie as Trie

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

-- | Disable display forms.
enableDisplayForms :: MonadTCM tcm => tcm a -> tcm a
enableDisplayForms =
  local $ \e -> e { envDisplayFormsEnabled = True }

-- | Disable display forms.
disableDisplayForms :: MonadTCM tcm => tcm a -> tcm a
disableDisplayForms =
  local $ \e -> e { envDisplayFormsEnabled = False }

-- | Check if display forms are enabled.
displayFormsEnabled :: MonadTCM tcm => tcm Bool
displayFormsEnabled = asks envDisplayFormsEnabled

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

setShowImplicitArguments :: MonadTCM tcm => Bool -> tcm a -> tcm a
setShowImplicitArguments showImp ret = do
  opts <- commandLineOptions
  let imp = optShowImplicit opts
  setCommandLineOptions $ opts { optShowImplicit = showImp }
  x <- ret
  opts <- commandLineOptions
  setCommandLineOptions $ opts { optShowImplicit = imp }
  return x

ignoreInterfaces :: MonadTCM tcm => tcm Bool
ignoreInterfaces = optIgnoreInterfaces <$> commandLineOptions

positivityCheckEnabled :: MonadTCM tcm => tcm Bool
positivityCheckEnabled = not . optDisablePositivity <$> commandLineOptions

getVerbosity :: MonadTCM tcm => tcm (Trie String Int)
getVerbosity = optVerbose <$> commandLineOptions

type VerboseKey = String

verboseS :: MonadTCM tcm => VerboseKey -> Int -> tcm () -> tcm ()
verboseS k n action = do
    t <- getVerbosity
    let ks = wordsBy (`elem` ".:") k
	m  = maximum $ 0 : Trie.lookupPath ks t
    when (n <= m) action

reportS :: MonadTCM tcm => VerboseKey -> Int -> String -> tcm ()
reportS k n s = verboseS k n $ liftIO $ putStr s

reportSLn :: MonadTCM tcm => VerboseKey -> Int -> String -> tcm ()
reportSLn k n s = verboseS k n $ liftIO $ putStrLn s

reportSDoc :: MonadTCM tcm => VerboseKey -> Int -> tcm Doc -> tcm ()
reportSDoc k n d = verboseS k n $ liftIO . print =<< d

verbose :: MonadTCM tcm => Int -> tcm () -> tcm ()
verbose = verboseS ""

report :: MonadTCM tcm => Int -> String -> tcm ()
report = reportS ""

reportLn :: MonadTCM tcm => Int -> String -> tcm ()
reportLn = reportSLn ""

reportDoc :: MonadTCM tcm => Int -> tcm Doc -> tcm ()
reportDoc = reportSDoc ""

