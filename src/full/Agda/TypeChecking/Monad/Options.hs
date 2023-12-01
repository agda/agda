
module Agda.TypeChecking.Monad.Options where

import Prelude hiding (null)

import Control.Monad          ( unless, when )
import Control.Monad.IO.Class ( MonadIO(..) )
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import qualified Data.Graph as Graph
import Data.List (sort)
import Data.Map (Map)
import qualified Data.Map as Map

import System.Directory
import System.FilePath

import Agda.Syntax.Common
import Agda.Syntax.TopLevelModuleName

import Agda.TypeChecking.Monad.Debug (reportSDoc)
import Agda.TypeChecking.Warnings
import Agda.TypeChecking.Monad.Base
import Agda.TypeChecking.Monad.Imports
import Agda.TypeChecking.Monad.State
import Agda.TypeChecking.Monad.Benchmark
import Agda.TypeChecking.Monad.Trace

import Agda.Interaction.FindFile
import Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens
import Agda.Interaction.Library
import Agda.Interaction.Library.Base (libAbove, libFile)

import Agda.Utils.FileName
import qualified Agda.Utils.Graph.AdjacencyMap.Unidirectional as G
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Null
import Agda.Syntax.Common.Pretty
import Agda.Utils.Size
import Agda.Utils.WithDefault

import Agda.Utils.Impossible

-- | Sets the pragma options.
--   Checks for unsafe combinations.
setPragmaOptions :: PragmaOptions -> TCM ()
setPragmaOptions opts = do
  -- Check for unsafe pragma options if @--safe@ is on.
  when (Lens.getSafeMode opts) $
    unlessNull (unsafePragmaOptions opts) $ \ unsafe ->
      warning $ SafeFlagPragma unsafe

  stPragmaOptions `setTCLens` opts
  updateBenchmarkingStatus

-- | Sets the command line options (both persistent and pragma options
-- are updated).
--
-- Relative include directories are made absolute with respect to the
-- current working directory. If the include directories have changed
-- then the state is reset (partly, see 'setIncludeDirs').
--
-- An empty list of relative include directories (@'Left' []@) is
-- interpreted as @["."]@.
setCommandLineOptions :: CommandLineOptions -> TCM ()
setCommandLineOptions opts = do
  root <- liftIO (absolute =<< getCurrentDirectory)
  setCommandLineOptions' root opts

setCommandLineOptions'
  :: AbsolutePath
     -- ^ The base directory of relative paths.
  -> CommandLineOptions
  -> TCM ()
setCommandLineOptions' root opts = do
  -- Andreas, 2022-11-19: removed a call to checkOpts which did nothing.
      incs <- case optAbsoluteIncludePaths opts of
        [] -> do
          opts' <- setLibraryPaths root opts
          let incs = optIncludePaths opts'
          setIncludeDirs incs root
          getIncludeDirs
        incs -> return incs
      modifyTC $ Lens.setCommandLineOptions opts{ optAbsoluteIncludePaths = incs }
      setPragmaOptions (optPragmaOptions opts)
      updateBenchmarkingStatus

libToTCM :: LibM a -> TCM a
libToTCM m = do
  cachedConfs <- useTC stProjectConfigs
  cachedLibs  <- useTC stAgdaLibFiles

  ((z, warns), (cachedConfs', cachedLibs')) <- liftIO $
    (`runStateT` (cachedConfs, cachedLibs)) $ runWriterT $ runExceptT m

  modifyTCLens stProjectConfigs $ const cachedConfs'
  modifyTCLens stAgdaLibFiles   $ const cachedLibs'

  unless (null warns) $ warnings $ map LibraryWarning warns
  case z of
    Left s  -> typeError $ GenericDocError s
    Right x -> return x

-- | Returns the library files for a given file.
--
-- Nothing is returned if 'optUseLibs' is 'False'.
--
-- An error is raised if 'optUseLibs' is 'True' and a library file is
-- located too far down the directory hierarchy (see
-- 'checkLibraryFileNotTooFarDown').

getAgdaLibFiles
  :: AbsolutePath        -- ^ The file name.
  -> TopLevelModuleName  -- ^ The top-level module name.
  -> TCM [AgdaLibFile]
getAgdaLibFiles f m = do
  ls <- getAgdaLibFilesWithoutTopLevelModuleName f
  mapM_ (checkLibraryFileNotTooFarDown m) ls
  return ls

-- | Returns potential library files for a file without a known
-- top-level module name.
--
-- Once the top-level module name is known one can use
-- 'checkLibraryFileNotTooFarDown' to check that the potential library
-- files were not located too far down the directory hierarchy.
--
-- Nothing is returned if 'optUseLibs' is 'False'.

getAgdaLibFilesWithoutTopLevelModuleName
  :: AbsolutePath  -- ^ The file.
  -> TCM [AgdaLibFile]
getAgdaLibFilesWithoutTopLevelModuleName f = do
  useLibs <- optUseLibs <$> commandLineOptions
  if | useLibs   -> libToTCM $ mkLibM [] $ getAgdaLibFiles' root
     | otherwise -> return []
  where
  root = takeDirectory $ filePath f

-- | Checks that a library file for the module @A.B.C@ (say) in the
-- directory @dir/A/B@ is located at least two directories above the
-- file (not in @dir/A@ or @dir/A/B@).

checkLibraryFileNotTooFarDown ::
  TopLevelModuleName ->
  AgdaLibFile ->
  TCM ()
checkLibraryFileNotTooFarDown m lib =
  when (lib ^. libAbove < size m - 1) $ typeError $ GenericError $
    "A .agda-lib file for " ++ prettyShow m ++
    " must not be located in the directory " ++
    takeDirectory (lib ^. libFile)

-- | Returns the library options for a given file.

getLibraryOptions
  :: AbsolutePath        -- ^ The file name.
  -> TopLevelModuleName  -- ^ The top-level module name.
  -> TCM [OptionsPragma]
getLibraryOptions f m = map _libPragmas <$> getAgdaLibFiles f m

setLibraryPaths
  :: AbsolutePath
     -- ^ The base directory of relative paths.
  -> CommandLineOptions
  -> TCM CommandLineOptions
setLibraryPaths root o =
  setLibraryIncludes =<< addDefaultLibraries root o

setLibraryIncludes :: CommandLineOptions -> TCM CommandLineOptions
setLibraryIncludes o
  | not (optUseLibs o) = pure o
  | otherwise = do
    let libs = optLibraries o
    installed <- libToTCM $ getInstalledLibraries (optOverrideLibrariesFile o)
    paths     <- libToTCM $ libraryIncludePaths (optOverrideLibrariesFile o) installed libs
    return o{ optIncludePaths = paths ++ optIncludePaths o }

addDefaultLibraries
  :: AbsolutePath
     -- ^ The base directory of relative paths.
  -> CommandLineOptions
  -> TCM CommandLineOptions
addDefaultLibraries root o
  | not (null $ optLibraries o) || not (optUseLibs o) = pure o
  | otherwise = do
  (libs, incs) <- libToTCM $ getDefaultLibraries (filePath root) (optDefaultLibs o)
  return o{ optIncludePaths = incs ++ optIncludePaths o, optLibraries = libs }

-- This function is only called when an interactor exists
-- (i.e. when Agda actually does something).
addTrustedExecutables
  :: CommandLineOptions
  -> TCM CommandLineOptions
addTrustedExecutables o = do
  trustedExes <- libToTCM $ getTrustedExecutables
  -- Wen, 2020-06-03
  -- Replace the map wholesale instead of computing the union because this function
  -- should never be called more than once, and doing so either has the same result
  -- or is a security risk.
  return o{ optTrustedExecutables = trustedExes }

setOptionsFromPragma :: OptionsPragma -> TCM ()
setOptionsFromPragma ps = setCurrentRange (pragmaRange ps) $ do
    opts <- commandLineOptions
    let (z, warns) = runOptM (parsePragmaOptions ps opts)
    mapM_ (warning . OptionWarning) warns
    case z of
      Left err    -> typeError $ GenericError err
      Right opts' -> setPragmaOptions opts'

-- | Disable display forms.
enableDisplayForms :: MonadTCEnv m => m a -> m a
enableDisplayForms =
  localTC $ \e -> e { envDisplayFormsEnabled = True }

-- | Disable display forms.
disableDisplayForms :: MonadTCEnv m => m a -> m a
disableDisplayForms =
  localTC $ \e -> e { envDisplayFormsEnabled = False }

-- | Check if display forms are enabled.
displayFormsEnabled :: MonadTCEnv m => m Bool
displayFormsEnabled = asksTC envDisplayFormsEnabled

-- | Gets the include directories.
--
-- Precondition: 'optAbsoluteIncludePaths' must be nonempty (i.e.
-- 'setCommandLineOptions' must have run).

getIncludeDirs :: HasOptions m => m [AbsolutePath]
getIncludeDirs = do
  incs <- optAbsoluteIncludePaths <$> commandLineOptions
  case incs of
    [] -> __IMPOSSIBLE__
    _  -> return incs

-- | Makes the given directories absolute and stores them as include
-- directories.
--
-- If the include directories change, then the state is reset
-- (completely, except for the include directories and some other
-- things).
--
-- An empty list is interpreted as @["."]@.

setIncludeDirs :: [FilePath]    -- ^ New include directories.
               -> AbsolutePath  -- ^ The base directory of relative paths.
               -> TCM ()
setIncludeDirs incs root = do
  -- save the previous include dirs
  oldIncs <- getsTC Lens.getAbsoluteIncludePaths

  -- Add the current dir if no include path is given
  incs <- return $ if null incs then ["."] else incs
  -- Make paths absolute
  incs <- return $  map (mkAbsolute . (filePath root </>)) incs

  -- Andreas, 2013-10-30  Add default include dir
      -- NB: This is an absolute file name, but
      -- Agda.Utils.FilePath wants to check absoluteness anyway.
  primdir <- liftIO $ mkAbsolute <$> getPrimitiveLibDir
      -- We add the default dir at the end, since it is then
      -- printed last in error messages.
      -- Might also be useful to overwrite default imports...
  incs <- return $ nubOn id $ incs ++ [primdir]

  reportSDoc "setIncludeDirs" 10 $ return $ vcat
    [ "Old include directories:"
    , nest 2 $ vcat $ map pretty oldIncs
    , "New include directories:"
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
  when (sort oldIncs /= sort incs) $ do
    ho <- getInteractionOutputCallback
    tcWarnings <- useTC stTCWarnings -- restore already generated warnings
    projectConfs <- useTC stProjectConfigs  -- restore cached project configs & .agda-lib
    agdaLibFiles <- useTC stAgdaLibFiles    -- files, since they use absolute paths
    decodedModules <- getDecodedModules
    (keptDecodedModules, modFile) <- modulesToKeep incs decodedModules
    resetAllState
    setTCLens stTCWarnings tcWarnings
    setTCLens stProjectConfigs projectConfs
    setTCLens stAgdaLibFiles agdaLibFiles
    setInteractionOutputCallback ho
    setDecodedModules keptDecodedModules
    setTCLens stModuleToSource modFile

  Lens.putAbsoluteIncludePaths incs
  where
  -- A decoded module is kept if its top-level module name is resolved
  -- to the same absolute path using the old and the new include
  -- directories, and the same applies to all dependencies.
  --
  -- File system accesses are cached using the ModuleToSource data
  -- structure: For the old include directories this should mean that
  -- the file system is not accessed, but the file system is accessed
  -- for the new include directories, and certain changes to the file
  -- system could lead to interfaces being discarded. A new
  -- ModuleToSource structure, constructed using the new include
  -- directories, is returned.
  modulesToKeep
    :: [AbsolutePath]  -- New include directories.
    -> DecodedModules  -- Old decoded modules.
    -> TCM (DecodedModules, ModuleToSource)
  modulesToKeep incs old = process Map.empty Map.empty modules
    where
    -- A graph with one node per module in old, and an edge from m to
    -- n if the module corresponding to m imports the module
    -- corresponding to n.
    dependencyGraph :: G.Graph TopLevelModuleName ()
    dependencyGraph =
      G.fromNodes
        [ iTopLevelModuleName $ miInterface m
        | m <- Map.elems old
        ]
        `G.union`
      G.fromEdges
        [ G.Edge
            { source = iTopLevelModuleName $ miInterface m
            , target = d
            , label = ()
            }
        | m      <- Map.elems old
        , (d, _) <- iImportedModules $ miInterface m
        ]

    -- All the modules from old, sorted so that all of a module's
    -- dependencies precede it in the list.
    modules :: [ModuleInfo]
    modules =
      map (\case
              Graph.CyclicSCC{} ->
                -- Agda does not allow cycles in the dependency graph.
                __IMPOSSIBLE__
              Graph.AcyclicSCC m ->
                case Map.lookup m old of
                  Just m  -> m
                  Nothing -> __IMPOSSIBLE__) $
      G.sccs' dependencyGraph

    process ::
      Map TopLevelModuleName ModuleInfo -> ModuleToSource ->
      [ModuleInfo] -> TCM (DecodedModules, ModuleToSource)
    process !keep !modFile [] = return
      ( Map.fromList $
        Map.toList keep
      , modFile
      )
    process keep modFile (m : ms) = do
      let deps     = map fst $ iImportedModules $ miInterface m
          depsKept = all (`Map.member` keep) deps
      (keep, modFile) <-
        if not depsKept then return (keep, modFile) else do
        let t = iTopLevelModuleName $ miInterface m
        oldF            <- findFile' t
        (newF, modFile) <- liftIO $ findFile'' incs t modFile
        return $ case (oldF, newF) of
          (Right f1, Right f2) | f1 == f2 ->
            (Map.insert t m keep, modFile)
          _ -> (keep, modFile)
      process keep modFile ms

isPropEnabled :: HasOptions m => m Bool
isPropEnabled = optProp <$> pragmaOptions

isLevelUniverseEnabled :: HasOptions m => m Bool
isLevelUniverseEnabled = optLevelUniverse <$> pragmaOptions

isTwoLevelEnabled :: HasOptions m => m Bool
isTwoLevelEnabled = optTwoLevel <$> pragmaOptions

{-# SPECIALIZE hasUniversePolymorphism :: TCM Bool #-}
hasUniversePolymorphism :: HasOptions m => m Bool
hasUniversePolymorphism = optUniversePolymorphism <$> pragmaOptions

showImplicitArguments :: HasOptions m => m Bool
showImplicitArguments = optShowImplicit <$> pragmaOptions

showGeneralizedArguments :: HasOptions m => m Bool
showGeneralizedArguments = (\opt -> optShowGeneralized opt) <$> pragmaOptions

showIrrelevantArguments :: HasOptions m => m Bool
showIrrelevantArguments = optShowIrrelevant <$> pragmaOptions

showIdentitySubstitutions :: HasOptions m => m Bool
showIdentitySubstitutions = optShowIdentitySubstitutions <$> pragmaOptions

-- | Switch on printing of implicit and irrelevant arguments.
--   E.g. for reification in with-function generation.
--
--   Restores all 'PragmaOptions' after completion.
--   Thus, do not attempt to make persistent 'PragmaOptions'
--   changes in a `withShowAllArguments` bracket.

withShowAllArguments :: ReadTCState m => m a -> m a
withShowAllArguments = withShowAllArguments' True

withShowAllArguments' :: ReadTCState m => Bool -> m a -> m a
withShowAllArguments' yes = withPragmaOptions $ \ opts ->
  opts { _optShowImplicit = Value yes, _optShowIrrelevant = Value yes }

withoutPrintingGeneralization :: ReadTCState m => m a -> m a
withoutPrintingGeneralization = withPragmaOptions $ \ opts ->
  opts { _optShowGeneralized = Value False }

-- | Change 'PragmaOptions' for a computation and restore afterwards.
withPragmaOptions :: ReadTCState m => (PragmaOptions -> PragmaOptions) -> m a -> m a
withPragmaOptions = locallyTCState stPragmaOptions

positivityCheckEnabled :: HasOptions m => m Bool
positivityCheckEnabled = optPositivityCheck <$> pragmaOptions

{-# SPECIALIZE typeInType :: TCM Bool #-}
typeInType :: HasOptions m => m Bool
typeInType = not . optUniverseCheck <$> pragmaOptions

etaEnabled :: HasOptions m => m Bool
etaEnabled = optEta <$> pragmaOptions

maxInstanceSearchDepth :: HasOptions m => m Int
maxInstanceSearchDepth = optInstanceSearchDepth <$> pragmaOptions

maxInversionDepth :: HasOptions m => m Int
maxInversionDepth = optInversionMaxDepth <$> pragmaOptions

-- | Returns the 'Language' currently in effect.

getLanguage :: HasOptions m => m Language
getLanguage = do
  opts <- pragmaOptions
  return $
    if not (optWithoutK opts) then WithK else
    case optCubical opts of
      Just variant -> Cubical variant
      Nothing      -> WithoutK
