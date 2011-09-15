{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Options where

import Control.Monad.Reader
import Control.Monad.State
import Data.Maybe
import Text.PrettyPrint
import qualified Agda.Utils.IO.Locale as LocIO
import System.Directory
import System.FilePath

import Agda.Syntax.Concrete
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.State
import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Utils.FileName
import Agda.Utils.Monad
import Agda.Utils.List
import Agda.Utils.Trie (Trie)
import qualified Agda.Utils.Trie as Trie

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Sets the pragma options.

setPragmaOptions :: PragmaOptions -> TCM ()
setPragmaOptions opts = do
  clo <- commandLineOptions
  case checkOpts (clo { optPragmaOptions = opts }) of
    Left err   -> __IMPOSSIBLE__
    Right opts -> do
      modify $ \s -> s { stPragmaOptions = (optPragmaOptions opts) }
-- | Sets the command line options (both persistent and pragma options
-- are updated).
--
-- Relative include directories are made absolute with respect to the
-- current working directory. If the include directories have changed,
-- then the state is reset.
--
-- An empty list of relative include directories (@'Left' []@) is
-- interpreted as @["."]@.

setCommandLineOptions :: CommandLineOptions -> TCM ()
setCommandLineOptions opts =
  case checkOpts opts of
    Left err   -> __IMPOSSIBLE__
    Right opts -> do
      incs <- case optIncludeDirs opts of
        Right is -> return is
        Left  is -> do
          setIncludeDirs is CurrentDir
          getIncludeDirs
      modify $ \s ->
        s { stPersistentOptions = opts { optIncludeDirs = Right incs }
          , stPragmaOptions     = optPragmaOptions opts
          }

-- | Returns the pragma options which are currently in effect.

pragmaOptions :: TCM PragmaOptions
pragmaOptions = gets stPragmaOptions

-- | Returns the command line options which are currently in effect.

commandLineOptions :: TCM CommandLineOptions
commandLineOptions = do
  p  <- gets stPragmaOptions
  cl <- gets stPersistentOptions
  return $ cl { optPragmaOptions = p }

setOptionsFromPragma :: OptionsPragma -> TCM ()
setOptionsFromPragma ps = do
    opts <- commandLineOptions
    case parsePragmaOptions ps opts of
	Left err    -> typeError $ GenericError err
	Right opts' -> setPragmaOptions opts'

-- | Disable display forms.
enableDisplayForms :: TCM a -> TCM a
enableDisplayForms =
  local $ \e -> e { envDisplayFormsEnabled = True }

-- | Disable display forms.
disableDisplayForms :: TCM a -> TCM a
disableDisplayForms =
  local $ \e -> e { envDisplayFormsEnabled = False }

-- | Check if display forms are enabled.
displayFormsEnabled :: TCM Bool
displayFormsEnabled = asks envDisplayFormsEnabled

-- | Don't eta contract implicit
dontEtaContractImplicit :: TCM a -> TCM a
dontEtaContractImplicit = local $ \e -> e { envEtaContractImplicit = False }

-- | Do eta contract implicit
{-# SPECIALIZE doEtaContractImplicit :: TCM a -> TCM a #-}
doEtaContractImplicit :: MonadTCM tcm => tcm a -> tcm a
doEtaContractImplicit = local $ \e -> e { envEtaContractImplicit = True }

shouldEtaContractImplicit :: TCM Bool
shouldEtaContractImplicit = asks envEtaContractImplicit

-- | Don't reify interaction points
dontReifyInteractionPoints :: TCM a -> TCM a
dontReifyInteractionPoints =
  local $ \e -> e { envReifyInteractionPoints = False }

shouldReifyInteractionPoints :: TCM Bool
shouldReifyInteractionPoints = asks envReifyInteractionPoints

-- | Gets the include directories.
--
-- Precondition: 'optIncludeDirs' must be @'Right' something@.

getIncludeDirs :: TCM [AbsolutePath]
getIncludeDirs = do
  incs <- optIncludeDirs <$> commandLineOptions
  case incs of
    Left  _    -> __IMPOSSIBLE__
    Right incs -> return incs

-- | Which directory should form the base of relative include paths?

data RelativeTo
  = ProjectRoot AbsolutePath
    -- ^ The root directory of the \"project\" containing the given
    -- file. The file needs to be syntactically correct, with a module
    -- name matching the file name.
  | CurrentDir
    -- ^ The current working directory.

-- | Makes the given directories absolute and stores them as include
-- directories.
--
-- If the include directories have changed, then the state is reset.
--
-- An empty list is interpreted as @["."]@.

setIncludeDirs
  :: [FilePath]
  -- ^ New include directories.
  -> RelativeTo
  -- ^ How should relative paths be interpreted?
  -> TCM ()
setIncludeDirs incs relativeTo = do
  opts <- commandLineOptions
  let oldIncs = optIncludeDirs opts

  (root, check) <- case relativeTo of
    CurrentDir -> do
      root <- liftIO (absolute =<< getCurrentDirectory)
      return (root, return ())
    ProjectRoot f -> do
      m <- moduleName' f
      return (projectRoot f m, checkModuleName m f)

  modify $ \s -> s { stPersistentOptions =
    (stPersistentOptions s) { optIncludeDirs =
      Right $ map (mkAbsolute . (filePath root </>)) $
        case incs of
          [] -> ["."]
          _  -> incs } }

  incs <- getIncludeDirs
  case oldIncs of
    Right incs' | incs' /= incs -> resetState
    _                           -> return ()

  check

setInputFile :: FilePath -> TCM ()
setInputFile file =
    do	opts <- commandLineOptions
	setCommandLineOptions $
          opts { optInputFile = Just file }

-- | Should only be run if 'hasInputFile'.
getInputFile :: TCM AbsolutePath
getInputFile =
    do	mf <- optInputFile <$> commandLineOptions
	case mf of
	    Just file -> liftIO $ absolute file
	    Nothing   -> __IMPOSSIBLE__

hasInputFile :: TCM Bool
hasInputFile = isJust <$> optInputFile <$> commandLineOptions

proofIrrelevance :: TCM Bool
proofIrrelevance = optProofIrrelevance <$> pragmaOptions

hasUniversePolymorphism :: TCM Bool
hasUniversePolymorphism = optUniversePolymorphism <$> pragmaOptions

showImplicitArguments :: TCM Bool
showImplicitArguments = optShowImplicit <$> pragmaOptions

setShowImplicitArguments :: Bool -> TCM a -> TCM a
setShowImplicitArguments showImp ret = do
  opts <- pragmaOptions
  let imp = optShowImplicit opts
  setPragmaOptions $ opts { optShowImplicit = showImp }
  x <- ret
  opts <- pragmaOptions
  setPragmaOptions $ opts { optShowImplicit = imp }
  return x

ignoreInterfaces :: TCM Bool
ignoreInterfaces = optIgnoreInterfaces <$> commandLineOptions

positivityCheckEnabled :: TCM Bool
positivityCheckEnabled = not . optDisablePositivity <$> pragmaOptions

typeInType :: TCM Bool
typeInType = not . optUniverseCheck <$> pragmaOptions

getVerbosity :: TCM (Trie String Int)
getVerbosity = optVerbose <$> pragmaOptions

type VerboseKey = String

hasVerbosity :: VerboseKey -> Int -> TCM Bool
hasVerbosity k n | n < 0     = __IMPOSSIBLE__
                 | otherwise = do
    t <- getVerbosity
    let ks = wordsBy (`elem` ".:") k
	m  = maximum $ 0 : Trie.lookupPath ks t
    return (n <= m)

-- | Precondition: The level must be non-negative.
verboseS :: VerboseKey -> Int -> TCM () -> TCM ()
verboseS k n action = whenM (hasVerbosity k n) action

reportS :: VerboseKey -> Int -> String -> TCM ()
reportS k n s = verboseS k n $ liftIO $ LocIO.putStr s

reportSLn :: VerboseKey -> Int -> String -> TCM ()
reportSLn k n s = verboseS k n $ liftIO $ LocIO.putStrLn s >> LocIO.stdoutFlush

reportSDoc :: VerboseKey -> Int -> TCM Doc -> TCM ()
reportSDoc k n d = verboseS k n $ liftIO . LocIO.print =<< d

verboseBracket :: VerboseKey -> Int -> String -> TCM a -> TCM a
verboseBracket k n s m = do
  v <- hasVerbosity k n
  if not v then m
           else do
    liftIO $ LocIO.putStrLn $ "{ " ++ s
    x <- m `finally` liftIO (LocIO.putStrLn "}")
    return x
