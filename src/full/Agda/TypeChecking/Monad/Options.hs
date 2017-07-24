{-# LANGUAGE CPP #-}

module Agda.TypeChecking.Monad.Options where

import Prelude hiding (mapM)

import Control.Applicative
import Control.Monad.Reader hiding (mapM)
import Control.Monad.State  hiding (mapM)

import Data.Maybe
import Data.Traversable

import System.Directory
import System.FilePath

import Agda.Syntax.Internal
import Agda.Syntax.Common
import Agda.Syntax.Concrete
import {-# SOURCE #-} Agda.TypeChecking.Monad.Debug
import {-# SOURCE #-} Agda.TypeChecking.Errors
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Benchmark
import {-# SOURCE #-} Agda.Interaction.FindFile
import Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens
import Agda.Interaction.Response
import Agda.Interaction.Library

import Agda.Utils.Except ( MonadError(catchError) )
import Agda.Utils.FileName
import Agda.Utils.Maybe
import Agda.Utils.Monad
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Pretty
import Agda.Utils.Trie (Trie)
import qualified Agda.Utils.Trie as Trie
import Agda.Utils.Except
import Agda.Utils.Either

#include "undefined.h"
import Agda.Utils.Impossible

-- | Sets the pragma options.

setPragmaOptions :: PragmaOptions -> TCM ()
setPragmaOptions opts = do
  stPragmaOptions %= Lens.mapSafeMode (Lens.getSafeMode opts ||)
  clo <- commandLineOptions
  let unsafe = unsafePragmaOptions opts
  when (Lens.getSafeMode clo && not (null unsafe)) $ warning $ SafeFlagPragma unsafe
  ok <- liftIO $ runOptM $ checkOpts (clo { optPragmaOptions = opts })
  case ok of
    Left err   -> __IMPOSSIBLE__
    Right opts -> do
      stPragmaOptions .= optPragmaOptions opts
      updateBenchmarkingStatus

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
setCommandLineOptions = setCommandLineOptions' CurrentDir

setCommandLineOptions' :: RelativeTo -> CommandLineOptions -> TCM ()
setCommandLineOptions' relativeTo opts = do
  z <- liftIO $ runOptM $ checkOpts opts
  case z of
    Left err   -> __IMPOSSIBLE__
    Right opts -> do
      incs <- case optAbsoluteIncludePaths opts of
        [] -> do
          opts' <- setLibraryPaths relativeTo opts
          let incs = optIncludePaths opts'
          setIncludeDirs incs relativeTo
          getIncludeDirs
        incs -> return incs
      modify $ Lens.setCommandLineOptions opts{ optAbsoluteIncludePaths = incs }
      setPragmaOptions (optPragmaOptions opts)
      updateBenchmarkingStatus

libToTCM :: LibM a -> TCM a
libToTCM m = do
  z <- liftIO $ runExceptT m
  case z of
    Left s  -> typeError $ GenericDocError s
    Right x -> return x

setLibraryPaths :: RelativeTo -> CommandLineOptions -> TCM CommandLineOptions
setLibraryPaths rel o = setLibraryIncludes =<< addDefaultLibraries rel o

setLibraryIncludes :: CommandLineOptions -> TCM CommandLineOptions
setLibraryIncludes o = do
    let libs = optLibraries o
    installed <- libToTCM $ getInstalledLibraries (optOverrideLibrariesFile o)
    paths     <- libToTCM $ libraryIncludePaths (optOverrideLibrariesFile o) installed libs
    return o{ optIncludePaths = paths ++ optIncludePaths o }

addDefaultLibraries :: RelativeTo -> CommandLineOptions -> TCM CommandLineOptions
addDefaultLibraries rel o
  | or [ not $ null $ optLibraries o
       , not $ optUseLibs o
       , optShowVersion o ] = pure o
  | otherwise = do
  root <- getProjectRoot rel
  (libs, incs) <- libToTCM $ getDefaultLibraries (filePath root) (optDefaultLibs o)
  return o{ optIncludePaths = incs ++ optIncludePaths o, optLibraries = libs }

setOptionsFromPragma :: OptionsPragma -> TCM ()
setOptionsFromPragma ps = do
    opts <- commandLineOptions
    z    <- liftIO $ runOptM (parsePragmaOptions ps opts)
    case z of
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

-- | Gets the include directories.
--
-- Precondition: 'optAbsoluteIncludePaths' must be nonempty (i.e.
-- 'setCommandLineOptions' must have run).

getIncludeDirs :: TCM [AbsolutePath]
getIncludeDirs = do
  incs <- optAbsoluteIncludePaths <$> commandLineOptions
  case incs of
    [] -> __IMPOSSIBLE__
    _  -> return incs

-- | Which directory should form the base of relative include paths?

data RelativeTo
  = ProjectRoot AbsolutePath
    -- ^ The root directory of the \"project\" containing the given
    -- file. The file needs to be syntactically correct, with a module
    -- name matching the file name.
  | CurrentDir
    -- ^ The current working directory.

getProjectRoot :: RelativeTo -> TCM AbsolutePath
getProjectRoot CurrentDir = liftIO (absolute =<< getCurrentDirectory)
getProjectRoot (ProjectRoot f) = do
  m <- moduleName' f
  return (projectRoot f m)

-- | Makes the given directories absolute and stores them as include
-- directories.
--
-- If the include directories change, then the state is reset (completely,
-- except for the include directories and 'stInteractionOutputCallback').
--
-- An empty list is interpreted as @["."]@.

setIncludeDirs :: [FilePath] -- ^ New include directories.
               -> RelativeTo -- ^ How should relative paths be interpreted?
               -> TCM ()
setIncludeDirs incs relativeTo = do
  -- save the previous include dirs
  oldIncs <- gets Lens.getAbsoluteIncludePaths

  root <- getProjectRoot relativeTo

  -- Add the current dir if no include path is given
  incs <- return $ if null incs then ["."] else incs
  -- Make paths absolute
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

  reportSDoc "setIncludeDirs" 10 $ return $ vcat
    [ text "Old include directories:"
    , nest 2 $ vcat $ map pretty oldIncs
    , text "New include directories:"
    , nest 2 $ vcat $ map pretty incs
    ]

  -- Check whether the include dirs have changed.  If yes, reset state.
  -- Andreas, 2013-10-30 comments:
  -- The logic, namely using the include-dirs variable as a driver
  -- for the interaction, qualifies for a code-obfuscation contest.
  -- I guess one Boolean more in the state cost 10.000 EUR at the time
  -- of this implementation...
  --
  -- Andreas, perhaps you have misunderstood something: If the include
  -- directories have changed and we do not reset the decoded modules,
  -- then we might (depending on how the rest of the code works) end
  -- up in a situation in which we use the contents of the file
  -- "old-path/M.agda", when the user actually meant
  -- "new-path/M.agda".
  when (oldIncs /= incs) $ do
    ho <- getInteractionOutputCallback
    resetAllState
    setInteractionOutputCallback ho

  Lens.putAbsoluteIncludePaths incs

  -- Andreas, 2016-07-11 (reconstructing semantics):
  --
  -- Check that the module name of the project root
  -- is still correct wrt. to the changed include path.
  --
  -- E.g. if the include path was "/" and file "/A/B" was named "module A.B",
  -- and then the include path changes to "/A/", the module name
  -- becomes invalid; correct would then be "module B".

  case relativeTo of
    CurrentDir -> return ()
    ProjectRoot f -> void $ moduleName f
     -- Andreas, 2016-07-12 WAS:
     -- do
     --  m <- moduleName' f
     --  checkModuleName m f Nothing


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

{-# SPECIALIZE sharedFun :: TCM (Term -> Term) #-}
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

enableCaching :: TCM Bool
enableCaching = optCaching <$> commandLineOptions

showImplicitArguments :: TCM Bool
showImplicitArguments = optShowImplicit <$> pragmaOptions

showIrrelevantArguments :: TCM Bool
showIrrelevantArguments = optShowIrrelevant <$> pragmaOptions

-- | Switch on printing of implicit and irrelevant arguments.
--   E.g. for reification in with-function generation.
--
--   Restores all 'PragmaOptions' after completion.
--   Thus, do not attempt to make persistent 'PragmaOptions'
--   changes in a `withShowAllArguments` bracket.

withShowAllArguments :: TCM a -> TCM a
withShowAllArguments = withShowAllArguments' True

withShowAllArguments' :: Bool -> TCM a -> TCM a
withShowAllArguments' yes = withPragmaOptions $ \ opts ->
  opts { optShowImplicit = yes, optShowIrrelevant = yes }

-- | Change 'PragmaOptions' for a computation and restore afterwards.

withPragmaOptions :: (PragmaOptions -> PragmaOptions) -> TCM a -> TCM a
withPragmaOptions f cont = do
  opts <- pragmaOptions
  setPragmaOptions $ f opts
  x <- cont
  setPragmaOptions opts
  return x


ignoreInterfaces :: TCM Bool
ignoreInterfaces = optIgnoreInterfaces <$> commandLineOptions

positivityCheckEnabled :: TCM Bool
positivityCheckEnabled = not . optDisablePositivity <$> pragmaOptions

{-# SPECIALIZE typeInType :: TCM Bool #-}
typeInType :: HasOptions m => m Bool
typeInType = not . optUniverseCheck <$> pragmaOptions

etaEnabled :: TCM Bool
etaEnabled = optEta <$> pragmaOptions

maxInstanceSearchDepth :: TCM Int
maxInstanceSearchDepth = optInstanceSearchDepth <$> pragmaOptions

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
        m  = last $ 0 : Trie.lookupPath ks t
    return (n <= m)

-- | Check whether a certain verbosity level is activated (exact match).

{-# SPECIALIZE hasExactVerbosity :: VerboseKey -> Int -> TCM Bool #-}
hasExactVerbosity :: HasOptions m => VerboseKey -> Int -> m Bool
hasExactVerbosity k n =
  (Just n ==) . Trie.lookup (wordsBy (`elem` ".:") k) <$> getVerbosity

-- | Run a computation if a certain verbosity level is activated (exact match).

{-# SPECIALIZE whenExactVerbosity :: VerboseKey -> Int -> TCM () -> TCM () #-}
whenExactVerbosity :: MonadTCM tcm => VerboseKey -> Int -> tcm () -> tcm ()
whenExactVerbosity k n = whenM $ liftTCM $ hasExactVerbosity k n

-- | Run a computation if a certain verbosity level is activated.
--
--   Precondition: The level must be non-negative.
{-# SPECIALIZE verboseS :: VerboseKey -> Int -> TCM () -> TCM () #-}
-- {-# SPECIALIZE verboseS :: MonadIO m => VerboseKey -> Int -> TCMT m () -> TCMT m () #-} -- RULE left-hand side too complicated to desugar
{-# SPECIALIZE verboseS :: MonadTCM tcm => VerboseKey -> Int -> tcm () -> tcm () #-}
verboseS :: HasOptions m => VerboseKey -> Int -> m () -> m ()
verboseS k n action = whenM (hasVerbosity k n) action
