{-# LANGUAGE CPP #-} -- GHC 7.4.2 requires this indentation. See Issue 1460.
{-# LANGUAGE FlexibleContexts #-}

module Agda.TypeChecking.Monad.Options where

import Prelude hiding (mapM)

import Control.Applicative
import Control.Monad.Reader hiding (mapM)
import Control.Monad.State  hiding (mapM)

import Data.Maybe
import Data.Traversable

import Text.PrettyPrint
import System.Directory
import System.FilePath

import Agda.Syntax.Internal
import Agda.Syntax.Concrete
import {-# SOURCE #-} Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.State
import Agda.Interaction.FindFile
import Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens
import Agda.Interaction.Response

import Agda.Utils.Except ( MonadError(catchError) )
import Agda.Utils.FileName
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Trie (Trie)
import qualified Agda.Utils.Trie as Trie

#include "undefined.h"
import Agda.Utils.Impossible

-- | Sets the pragma options.

setPragmaOptions :: PragmaOptions -> TCM ()
setPragmaOptions opts = do
  clo <- commandLineOptions
  let unsafe = unsafePragmaOptions opts
  when (optSafe clo && not (null unsafe)) $ typeError (SafeFlagPragma unsafe)
  case checkOpts (clo { optPragmaOptions = opts }) of
    Left err   -> __IMPOSSIBLE__
    Right opts -> do
      stPragmaOptions .= optPragmaOptions opts

-- | Sets the command line options (both persistent and pragma options
-- are updated).
--
-- Relative include directories are made absolute with respect to the
-- current working directory. If the include directories have changed
-- (thus, they are 'Left' now, and were previously @'Right' something@),
-- then the state is reset (completely, see setIncludeDirs) .
--
-- An empty list of relative include directories (@'Left' []@) is
-- interpreted as @["."]@.

setCommandLineOptions :: CommandLineOptions -> TCM ()
setCommandLineOptions opts =
  case checkOpts opts of
    Left err   -> __IMPOSSIBLE__
    Right opts -> do
      incs <- case optIncludeDirs opts of
        Right absolutePathes -> return absolutePathes
        Left  relativePathes -> do
          -- setIncludeDirs makes pathes (relative to CurrentDir) absolute
          -- and possible adds the current directory (if no pathes given)
          setIncludeDirs relativePathes CurrentDir
          getIncludeDirs
      modify $ Lens.setCommandLineOptions opts{ optIncludeDirs = Right incs }
             . Lens.setPragmaOptions (optPragmaOptions opts)

class (Functor m, Applicative m, Monad m) => HasOptions m where
  -- | Returns the pragma options which are currently in effect.
  pragmaOptions      :: m PragmaOptions
  -- | Returns the command line options which are currently in effect.
  commandLineOptions :: m CommandLineOptions

instance MonadIO m => HasOptions (TCMT m) where
  pragmaOptions = use stPragmaOptions

  commandLineOptions = do
    p  <- use stPragmaOptions
    cl <- stPersistentOptions . stPersistentState <$> get
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

{-# SPECIALIZE shouldEtaContractImplicit :: TCM Bool #-}
shouldEtaContractImplicit :: MonadReader TCEnv m => m Bool
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
-- If the include directories change (and they were previously
-- @'Right' something@), then the state is reset (completely, except
-- for the include directories and 'stInteractionOutputCallback').
--
-- An empty list is interpreted as @["."]@.

setIncludeDirs
  :: [FilePath]
  -- ^ New include directories.
  -> RelativeTo
  -- ^ How should relative paths be interpreted?
  -> TCM ()
setIncludeDirs incs relativeTo = do
  -- save the previous include dirs
  oldIncs <- gets Lens.getIncludeDirs

  (root, check) <- case relativeTo of
    CurrentDir -> do
      root <- liftIO (absolute =<< getCurrentDirectory)
      return (root, return ())
    ProjectRoot f -> do
      m <- moduleName' f
      return (projectRoot f m, checkModuleName m f)

  -- Add the current dir if no include path is given
  incs <- return $ if null incs then ["."] else incs
  -- Make pathes absolute
  incs <- return $  map (mkAbsolute . (filePath root </>)) incs

  -- Andreas, 2013-10-30  Add default include dir
  libdir <- liftIO $ defaultLibDir
      -- NB: This is an absolute file name, but
      -- Agda.Utils.FilePath wants to check absoluteness anyway.
  let primdir = mkAbsolute $ libdir </> "prim"
      -- We add the default dir at the end, since it is then
      -- printed last in error messages.
      -- Might also be useful to overwrite default imports...
  incs <- return $ incs ++ [primdir]
  Lens.putIncludeDirs $ Right $ incs

  -- Check whether the include dirs have changed.  If yes, reset state.
  -- Andreas, 2013-10-30 comments:
  -- The logic, namely using the include-dirs variable as a driver
  -- for the interaction, qualifies for a code-obfuscation contest.
  -- I guess one Boolean more in the state cost 10.000 EUR at the time
  -- of this implementation...
  case oldIncs of
    Right incs' | incs' /= incs -> do
      ho <- getInteractionOutputCallback
      resetAllState
      setInteractionOutputCallback ho
      Lens.putIncludeDirs $ Right incs
    _ -> return ()

  check

setInputFile :: FilePath -> TCM ()
setInputFile file =
    do  opts <- commandLineOptions
        setCommandLineOptions $
          opts { optInputFile = Just file }

-- | Should only be run if 'hasInputFile'.
getInputFile :: TCM AbsolutePath
getInputFile = fromMaybeM __IMPOSSIBLE__ $
  getInputFile'

-- | Return the 'optInputFile' as 'AbsolutePath', if any.
getInputFile' :: TCM (Maybe AbsolutePath)
getInputFile' = mapM (liftIO . absolute) =<< do
  optInputFile <$> commandLineOptions

hasInputFile :: TCM Bool
hasInputFile = isJust <$> optInputFile <$> commandLineOptions

proofIrrelevance :: TCM Bool
proofIrrelevance = optProofIrrelevance <$> pragmaOptions

{-# SPECIALIZE hasUniversePolymorphism :: TCM Bool #-}
hasUniversePolymorphism :: HasOptions m => m Bool
hasUniversePolymorphism = optUniversePolymorphism <$> pragmaOptions

{-# SPECIALIZE shared :: Term -> TCM Term #-}
sharedFun :: HasOptions m => m (Term -> Term)
sharedFun = do
  sharing <- optSharing <$> commandLineOptions
  return $ if sharing then shared_ else id

{-# SPECIALIZE shared :: Term -> TCM Term #-}
shared :: HasOptions m => Term -> m Term
shared v = ($ v) <$> sharedFun

{-# SPECIALIZE sharedType :: Type -> TCM Type #-}
sharedType :: HasOptions m => Type -> m Type
sharedType (El s v) = El s <$> shared v

showImplicitArguments :: TCM Bool
showImplicitArguments = optShowImplicit <$> pragmaOptions

showIrrelevantArguments :: TCM Bool
showIrrelevantArguments = optShowIrrelevant <$> pragmaOptions

-- | Switch on printing of implicit and irrelevant arguments.
--   E.g. for reification in with-function generation.
withShowAllArguments :: TCM a -> TCM a
withShowAllArguments ret = do
  opts <- pragmaOptions
  let imp = optShowImplicit opts
      irr = optShowIrrelevant opts
  setPragmaOptions $ opts { optShowImplicit = True, optShowIrrelevant = True }
  x <- ret
  opts <- pragmaOptions
  setPragmaOptions $ opts { optShowImplicit = imp, optShowIrrelevant = irr }
  return x

{- RETIRED, Andreas, 2012-04-30
setShowImplicitArguments :: Bool -> TCM a -> TCM a
setShowImplicitArguments showImp ret = do
  opts <- pragmaOptions
  let imp = optShowImplicit opts
  setPragmaOptions $ opts { optShowImplicit = showImp }
  x <- ret
  opts <- pragmaOptions
  setPragmaOptions $ opts { optShowImplicit = imp }
  return x
-}

ignoreInterfaces :: TCM Bool
ignoreInterfaces = optIgnoreInterfaces <$> commandLineOptions

positivityCheckEnabled :: TCM Bool
positivityCheckEnabled = not . optDisablePositivity <$> pragmaOptions

typeInType :: TCM Bool
typeInType = not . optUniverseCheck <$> pragmaOptions

------------------------------------------------------------------------
-- Verbosity

-- Invariant (which we may or may not currently break): Debug
-- printouts use one of the following functions:
--
--   reportS
--   reportSLn
--   reportSDoc

-- | Retrieve the current verbosity level.
{-# SPECIALIZE getVerbosity :: TCM (Trie String Int) #-}
getVerbosity :: HasOptions m => m (Trie String Int)
getVerbosity = optVerbose <$> pragmaOptions

type VerboseKey = String

-- | Check whether a certain verbosity level is activated.
--
--   Precondition: The level must be non-negative.
{-# SPECIALIZE hasVerbosity :: VerboseKey -> Int -> TCM Bool #-}
hasVerbosity :: HasOptions m => VerboseKey -> Int -> m Bool
hasVerbosity k n | n < 0     = __IMPOSSIBLE__
                 | otherwise = do
    t <- getVerbosity
    let ks = wordsBy (`elem` ".:") k
        m  = maximum $ 0 : Trie.lookupPath ks t
    return (n <= m)

-- | Displays a debug message in a suitable way.
{-# SPECIALIZE displayDebugMessage :: Int -> String -> TCM () #-}
displayDebugMessage :: MonadTCM tcm
  => Int     -- ^ The message's debug level.
  -> String  -- ^ Message.
  -> tcm ()
displayDebugMessage n s = liftTCM $
  appInteractionOutputCallback (Resp_RunningInfo n s)

-- | Run a computation if a certain verbosity level is activated.
--
--   Precondition: The level must be non-negative.
{-# SPECIALIZE verboseS :: VerboseKey -> Int -> TCM () -> TCM () #-}
verboseS :: MonadTCM tcm => VerboseKey -> Int -> tcm () -> tcm ()
verboseS k n action = whenM (liftTCM $ hasVerbosity k n) action

-- | Conditionally print debug string.
{-# SPECIALIZE reportS :: VerboseKey -> Int -> String -> TCM () #-}
reportS :: MonadTCM tcm => VerboseKey -> Int -> String -> tcm ()
reportS k n s = liftTCM $ verboseS k n $ displayDebugMessage n s

-- | Conditionally println debug string.
{-# SPECIALIZE reportSLn :: VerboseKey -> Int -> String -> TCM () #-}
reportSLn :: MonadTCM tcm => VerboseKey -> Int -> String -> tcm ()
reportSLn k n s = verboseS k n $
  displayDebugMessage n (s ++ "\n")

-- | Conditionally render debug 'Doc' and print it.
{-# SPECIALIZE reportSDoc :: VerboseKey -> Int -> TCM Doc -> TCM () #-}
reportSDoc :: MonadTCM tcm => VerboseKey -> Int -> TCM Doc -> tcm ()
reportSDoc k n d = liftTCM $ verboseS k n $ do
  displayDebugMessage n . (++ "\n") . show =<< do
    d `catchError` \ err ->
      (\ s -> (sep $ map text
                 [ "Printing debug message"
                 , k  ++ ":" ++show n
                 , "failed due to error:" ]) $$
              (nest 2 $ text s)) <$> prettyError err

-- | Print brackets around debug messages issued by a computation.
{-# SPECIALIZE verboseBracket :: VerboseKey -> Int -> String -> TCM a -> TCM a #-}
verboseBracket :: MonadTCM tcm => VerboseKey -> Int -> String -> TCM a -> tcm a
verboseBracket k n s m = liftTCM $ ifNotM (hasVerbosity k n) m $ {- else -} do
  displayDebugMessage n $ "{ " ++ s ++ "\n"
  m `finally` displayDebugMessage n "}\n"
