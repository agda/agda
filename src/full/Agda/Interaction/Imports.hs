{-# LANGUAGE CPP               #-}

{-| This module deals with finding imported modules and loading their
    interface files.
-}
module Agda.Interaction.Imports where

import Prelude hiding (null)

import Control.Arrow
import Control.DeepSeq
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Trans.Maybe
import qualified Control.Exception as E

import Data.Function (on)
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Foldable as Fold (toList)
import qualified Data.List as List
import Data.Maybe
import Data.Monoid (mempty, mappend)
import Data.Map (Map)
import Data.Set (Set)
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy as T

import System.Directory (doesFileExist, getModificationTime, removeFile)
import System.FilePath ((</>))

import qualified Text.PrettyPrint.Boxes as Boxes

import Agda.Benchmarking

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Parser
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Internal

import Agda.TypeChecking.Errors
import Agda.TypeChecking.Warnings
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.MetaVars ( openMetasToPostulates )
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Serialise
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Pretty as P
import Agda.TypeChecking.DeadCode
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TheTypeChecker

import Agda.Interaction.FindFile
import {-# SOURCE #-} Agda.Interaction.InteractionTop (showOpenMetas)
import Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens
import Agda.Interaction.Highlighting.Precise
  (HighlightingInfo, compress)
import Agda.Interaction.Highlighting.Generate
import Agda.Interaction.Highlighting.Vim
import Agda.Interaction.Response
  (RemoveTokenBasedHighlighting(KeepHighlighting))

import Agda.Utils.Except ( MonadError(catchError, throwError) )
import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Utils.Maybe
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.IO.Binary
import Agda.Utils.Pretty hiding (Mode)
import Agda.Utils.Time
import Agda.Utils.Hash
import qualified Agda.Utils.HashMap as HMap
import qualified Agda.Utils.Trie as Trie

#include "undefined.h"
import Agda.Utils.Impossible

-- | Some information about the source code.

data SourceInfo = SourceInfo
  { siSource     :: Text                  -- ^ Source code.
  , siFileType   :: FileType              -- ^ Source file type
  , siModule     :: C.Module              -- ^ The parsed module.
  , siModuleName :: C.TopLevelModuleName  -- ^ The top-level module name.
  }

-- | Computes a 'SourceInfo' record for the given file.

sourceInfo :: AbsolutePath -> TCM SourceInfo
sourceInfo f = Bench.billTo [Bench.Parsing] $ do
  source                <- runPM $ readFilePM f
  (parsedMod, fileType) <- runPM $
                           parseFile moduleParser f $ T.unpack source
  moduleName            <- moduleName f parsedMod
  return $ SourceInfo { siSource     = source
                      , siFileType   = fileType
                      , siModule     = parsedMod
                      , siModuleName = moduleName
                      }

-- | Is the aim to type-check the top-level module, or only to
-- scope-check it?

data Mode
  = ScopeCheck
  | TypeCheck
  deriving (Eq, Show)

-- | Are we loading the interface for the user-loaded file
--   or for an import?
data MainInterface
  = MainInterface Mode -- ^ For the main file.
                       --
                       --   In this case state changes inflicted by
                       --   'createInterface' are preserved.
  | NotMainInterface   -- ^ For an imported file.
                       --
                       --   In this case state changes inflicted by
                       --   'createInterface' are not preserved.
  deriving (Eq, Show)

-- | Should state changes inflicted by 'createInterface' be preserved?

includeStateChanges :: MainInterface -> Bool
includeStateChanges (MainInterface _) = True
includeStateChanges NotMainInterface  = False

-- | Merge an interface into the current proof state.
mergeInterface :: Interface -> TCM ()
mergeInterface i = do
    let sig     = iSignature i
        builtin = Map.toList $ iBuiltin i
        prim    = [ x | (_,Prim x) <- builtin ]
        bi      = Map.fromList [ (x,Builtin t) | (x,Builtin t) <- builtin ]
        warns   = iWarnings i
    bs <- getsTC stBuiltinThings
    reportSLn "import.iface.merge" 10 $ "Merging interface"
    reportSLn "import.iface.merge" 20 $
      "  Current builtins " ++ show (Map.keys bs) ++ "\n" ++
      "  New builtins     " ++ show (Map.keys bi)
    let check b = case (b1, b2) of
            (Builtin x, Builtin y)
              | x == y    -> return ()
              | otherwise -> typeError $ DuplicateBuiltinBinding b x y
            _ -> __IMPOSSIBLE__
          where
            Just b1 = Map.lookup b bs
            Just b2 = Map.lookup b bi
    mapM_ check (map fst $ Map.toList $ Map.intersection bs bi)
    addImportedThings sig bi (iPatternSyns i) (iDisplayForms i) (iUserWarnings i) warns
    reportSLn "import.iface.merge" 20 $
      "  Rebinding primitives " ++ show prim
    mapM_ rebind prim
    where
        rebind (x, q) = do
            PrimImpl _ pf <- lookupPrimitiveFunction x
            stImportedBuiltins `modifyTCLens` Map.insert x (Prim pf{ primFunName = q })

addImportedThings ::
  Signature -> BuiltinThings PrimFun ->
  A.PatternSynDefns -> DisplayForms -> Map A.QName String -> [TCWarning] -> TCM ()
addImportedThings isig ibuiltin patsyns display userwarn warnings = do
  stImports              `modifyTCLens` \ imp -> unionSignatures [imp, isig]
  stImportedBuiltins     `modifyTCLens` \ imp -> Map.union imp ibuiltin
  stImportedUserWarnings `modifyTCLens` \ imp -> Map.union imp userwarn
  stPatternSynImports    `modifyTCLens` \ imp -> Map.union imp patsyns
  stImportedDisplayForms `modifyTCLens` \ imp -> HMap.unionWith (++) imp display
  stTCWarnings           `modifyTCLens` \ imp -> List.union imp warnings
  addImportedInstances isig

-- | Scope checks the given module. A proper version of the module
-- name (with correct definition sites) is returned.

scopeCheckImport :: ModuleName -> TCM (ModuleName, Map ModuleName Scope)
scopeCheckImport x = do
    reportSLn "import.scope" 5 $ "Scope checking " ++ prettyShow x
    verboseS "import.scope" 10 $ do
      visited <- Map.keys <$> getVisitedModules
      reportSLn "import.scope" 10 $
        "  visited: " ++ List.intercalate ", " (map prettyShow visited)
    -- Since scopeCheckImport is called from the scope checker,
    -- we need to reimburse her account.
    i <- Bench.billTo [] $ getInterface x
    addImport x

    -- If that interface was supposed to raise a warning on import, do so.
    whenJust (iImportWarning i) $ warning . UserWarning

    -- let s = publicModules $ iInsideScope i
    let s = iScope i
    return (iModuleName i `withRangesOfQ` mnameToConcrete x, s)

data MaybeWarnings' a = NoWarnings | SomeWarnings a
  deriving (Show, Functor, Foldable, Traversable)
type MaybeWarnings = MaybeWarnings' [TCWarning]

applyFlagsToMaybeWarnings :: MaybeWarnings -> TCM MaybeWarnings
applyFlagsToMaybeWarnings mw = do
  w' <- traverse applyFlagsToTCWarnings mw
  return $ if null w' then NoWarnings else w'

instance Null a => Null (MaybeWarnings' a) where
  empty = NoWarnings
  null mws = case mws of
    NoWarnings      -> True
    SomeWarnings ws -> null ws

hasWarnings :: MaybeWarnings -> Bool
hasWarnings = not . null

-- | If the module has already been visited (without warnings), then
-- its interface is returned directly. Otherwise the computation is
-- used to find the interface and the computed interface is stored for
-- potential later use (unless the 'MainInterface' is @'MainInterface'
-- 'ScopeCheck'@).

alreadyVisited :: C.TopLevelModuleName ->
                  MainInterface ->
                  PragmaOptions ->
                  TCM (Interface, MaybeWarnings) ->
                  TCM (Interface, MaybeWarnings)
alreadyVisited x isMain currentOptions getIface = do
    mm <- getVisitedModule x
    case mm of
        -- A module with warnings should never be allowed to be
        -- imported from another module.
        Just mi | not (miWarnings mi) -> do
          reportSLn "import.visit" 10 $ "  Already visited " ++ prettyShow x
          let i = miInterface mi
          -- Check that imported options are compatible with current ones,
          -- but give primitive modules a pass
          optsCompat <- if miPrimitive mi then return True else do
            ifM (asksTC envCheckOptionConsistency)
            {-then-} (checkOptionsCompatible currentOptions (iOptionsUsed i)
                                             (iModuleName i))
            {-else-} (return True)
          if optsCompat then return (i , NoWarnings) else do
            wt <- getMaybeWarnings' isMain ErrorWarnings
            return (i, wt)
        _ -> do
          reportSLn "import.visit" 5 $ "  Getting interface for " ++ prettyShow x
          r@(i, wt) <- getIface
          reportSLn "import.visit" 5 $ "  Now we've looked at " ++ prettyShow x
          unless (isMain == MainInterface ScopeCheck) $
            visitModule $ ModuleInfo
              { miInterface  = i
              , miWarnings   = hasWarnings wt
              , miPrimitive  = False -- will be updated later for primitive modules
              }
          return r

-- | Type checks the main file of the interaction.
--   This could be the file loaded in the interacting editor (emacs),
--   or the file passed on the command line.
--
--   First, the primitive modules are imported.
--   Then, @getInterface'@ is called to do the main work.
--
--   If the 'Mode' is 'ScopeCheck', then type-checking is not
--   performed, only scope-checking. (This may include type-checking
--   of imported modules.) In this case the generated, partial
--   interface is not stored in the state ('stDecodedModules'). Note,
--   however, that if the file has already been type-checked, then a
--   complete interface is returned.

typeCheckMain
  :: AbsolutePath
     -- ^ The path to the file.
  -> Mode
     -- ^ Should the file be type-checked, or only scope-checked?
  -> SourceInfo
     -- ^ Information about the source code.
  -> TCM (Interface, MaybeWarnings)
typeCheckMain f mode si = do
  -- liftIO $ putStrLn $ "This is typeCheckMain " ++ prettyShow f
  -- liftIO . putStrLn . show =<< getVerbosity
  reportSLn "import.main" 10 $ "Importing the primitive modules."
  libdir <- liftIO defaultLibDir
  let libdirPrim = libdir </> "prim"
  reportSLn "import.main" 20 $ "Library dir = " ++ show libdir
  -- Turn off import-chasing messages.
  -- We have to modify the persistent verbosity setting, since
  -- getInterface resets the current verbosity settings to the persistent ones.
  bracket_ (getsTC Lens.getPersistentVerbosity) Lens.putPersistentVerbosity $ do
    Lens.modifyPersistentVerbosity (Trie.delete [])  -- set root verbosity to 0

    -- We don't want to generate highlighting information for Agda.Primitive.
    withHighlightingLevel None $ withoutOptionsChecking $
      forM_ (Set.map (libdirPrim </>) Lens.primitiveModules) $ \f -> do
        let file = mkAbsolute f
        si <- sourceInfo file
        checkModuleName' (siModuleName si) file
        _ <- getInterface_ (siModuleName si) (Just si)
        -- record that the just visited module is primitive
        mapVisitedModule (siModuleName si) (\ m -> m { miPrimitive = True })

  reportSLn "import.main" 10 $ "Done importing the primitive modules."

  -- Now do the type checking via getInterface'.
  checkModuleName' (siModuleName si) f
  getInterface' (siModuleName si) (MainInterface mode) (Just si)
  where
  checkModuleName' m f =
    -- Andreas, 2016-07-11, issue 2092
    -- The error range should be set to the file with the wrong module name
    -- not the importing one (which would be the default).
    (if null r then id else traceCall (SetRange r)) $
      checkModuleName m f Nothing
    where
    r = getRange m

-- | Tries to return the interface associated to the given (imported) module.
--   The time stamp of the relevant interface file is also returned.
--   Calls itself recursively for the imports of the given module.
--   May type check the module.
--   An error is raised if a warning is encountered.
--
--   Do not use this for the main file, use 'typeCheckMain' instead.

getInterface :: ModuleName -> TCM Interface
getInterface m = getInterface_ (toTopLevelModuleName m) Nothing

-- | See 'getInterface'.

getInterface_
  :: C.TopLevelModuleName
  -> Maybe SourceInfo
     -- ^ Optional information about the source code.
  -> TCM Interface
getInterface_ x msi = do
  (i, wt) <- getInterface' x NotMainInterface msi
  case wt of
    SomeWarnings w  -> tcWarningsToError (filter (notIM . tcWarning) w)
    NoWarnings      -> return i
   -- filter out unsolved interaction points for imported module so
   -- that we get the right error message (see test case Fail/Issue1296)
   where notIM UnsolvedInteractionMetas{} = False
         notIM _                          = True


-- | A more precise variant of 'getInterface'. If warnings are
-- encountered then they are returned instead of being turned into
-- errors.

getInterface'
  :: C.TopLevelModuleName
  -> MainInterface
  -> Maybe SourceInfo
     -- ^ Optional information about the source code.
  -> TCM (Interface, MaybeWarnings)
getInterface' x isMain msi = do
  withIncreasedModuleNestingLevel $ do
    -- Preserve the pragma options unless we are checking the main
    -- interface.
    bracket_ (useTC stPragmaOptions)
             (unless (includeStateChanges isMain) . (stPragmaOptions `setTCLens`)) $ do
     -- We remember but reset the pragma options locally
     -- For the main interface, we also remember the pragmas from the file
     when (includeStateChanges isMain) $ do
       pragmas <- concreteOptionsToOptionPragmas
                    (fst $ maybe __IMPOSSIBLE__ siModule msi)
       mapM_ setOptionsFromPragma pragmas
     currentOptions <- useTC stPragmaOptions
     -- Now reset the options
     setCommandLineOptions . stPersistentOptions . stPersistentState =<< getTC

     alreadyVisited x isMain currentOptions $ addImportCycleCheck x $ do
      file <- findFile x  -- requires source to exist

      reportSLn "import.iface" 10 $ "  Check for cycle"
      checkForImportCycle

      uptodate <- Bench.billTo [Bench.Import] $ do
        ignore <- (ignoreInterfaces `and2M`
                    (not <$> Lens.isBuiltinModule (filePath file)))
                  `or2M` ignoreAllInterfaces
        cached <- runMaybeT $ isCached x file
          -- If it's cached ignoreInterfaces has no effect;
          -- to avoid typechecking a file more than once.
        sourceH <- case msi of
                     Nothing -> liftIO $ hashTextFile file
                     Just si -> return $ hashText (siSource si)
        ifaceH  <-
          case cached of
            Nothing -> fmap fst <$> getInterfaceFileHashes (filePath $ toIFile file)
            Just i  -> return $ Just $ iSourceHash i
        let unchanged = Just sourceH == ifaceH
        return $ unchanged && (not ignore || isJust cached)

      reportSLn "import.iface" 5 $
        "  " ++ prettyShow x ++ " is " ++
        (if uptodate then "" else "not ") ++ "up-to-date."

      (stateChangesIncluded, (i, wt)) <- do
        -- -- Andreas, 2014-10-20 AIM XX:
        -- -- Always retype-check the main file to get the iInsideScope
        -- -- which is no longer serialized.
        -- let maySkip = isMain == NotMainInterface
        -- Andreas, 2015-07-13: Serialize iInsideScope again.
        let maySkip = True

        if uptodate && maySkip
          then getStoredInterface x file isMain msi
          else typeCheck          x file isMain msi

      -- Ensure that the given module name matches the one in the file.
      let topLevelName = toTopLevelModuleName $ iModuleName i
      unless (topLevelName == x) $ do
        -- Andreas, 2014-03-27 This check is now done in the scope checker.
        -- checkModuleName topLevelName file
        typeError $ OverlappingProjects file topLevelName x

      visited <- isVisited x
      reportSLn "import.iface" 5 $ if visited then "  We've been here. Don't merge."
                                   else "  New module. Let's check it out."

      -- Check that imported module options are consistent with
      -- current options (issue #2487)
      -- compute updated warnings if needed
      wt' <- ifM (not <$> asksTC envCheckOptionConsistency)
                 {- then -} (return wt) {- else -} $ do
        optComp <- checkOptionsCompatible currentOptions (iOptionsUsed i) (iModuleName i)
        -- we might have aquired some more warnings when consistency checking
        if optComp then return wt else getMaybeWarnings' isMain ErrorWarnings

      unless (visited || stateChangesIncluded) $ do
        mergeInterface i
        Bench.billTo [Bench.Highlighting] $
          ifTopLevelAndHighlightingLevelIs NonInteractive $
            highlightFromInterface i file

      stCurrentModule `setTCLens` Just (iModuleName i)

      -- Interfaces are not stored if we are only scope-checking, or
      -- if any warnings were encountered.
      case (isMain, wt') of
        (MainInterface ScopeCheck, _) -> return ()
        (_, SomeWarnings w)           -> return ()
        _                             -> storeDecodedModule i

      reportSLn "warning.import" 10 $ unlines $
        [ "module: " ++ show (C.moduleNameParts x)
        , "WarningOnImport: " ++ show (iImportWarning i)
        ]
      return (i, wt')

-- | Check if the options used for checking an imported module are
--   compatible with the current options. Raises Non-fatal errors if
--   not.
checkOptionsCompatible :: PragmaOptions -> PragmaOptions -> ModuleName -> TCM Bool
checkOptionsCompatible current imported importedModule = flip execStateT True $ do
  reportSDoc "import.iface.options" 5 $ P.nest 2 $ "current options  =" P.<+> showOptions current
  reportSDoc "import.iface.options" 5 $ P.nest 2 $ "imported options =" P.<+> showOptions imported
  forM_ coinfectiveOptions $ \ (opt, optName) -> do
    unless ((opt current) `implies` (opt imported)) $ do
      put False
      warning (CoInfectiveImport optName importedModule)
  forM_ infectiveOptions $ \ (opt, optName) -> do
    unless ((opt imported) `implies` (opt current)) $ do
      put False
      warning (InfectiveImport optName importedModule)
  where
    implies :: Bool -> Bool -> Bool
    p `implies` q = p <= q

    showOptions opts = P.prettyList (map (\ (o, n) -> P.text n P.<> ": " P.<+> (P.pretty $ o opts))
                                 (coinfectiveOptions ++ infectiveOptions))

-- | Check whether interface file exists and is in cache
--   in the correct version (as testified by the interface file hash).

isCached
  :: C.TopLevelModuleName
     -- ^ Module name of file we process.
  -> AbsolutePath
     -- ^ File we process.
  -> MaybeT TCM Interface

isCached x file = do
  let ifile = filePath $ toIFile file

  -- Make sure the file exists in the case sensitive spelling.
  guardM $ liftIO $ doesFileExistCaseSensitive ifile

  -- Check that we have cached the module.
  mi <- MaybeT $ getDecodedModule x

  -- Check that the interface file exists and return its hash.
  h  <- MaybeT $ fmap snd <$> getInterfaceFileHashes ifile

  -- Make sure the hashes match.
  guard $ iFullHash mi == h

  return mi

-- | Try to get the interface from interface file or cache.

getStoredInterface
  :: C.TopLevelModuleName
     -- ^ Module name of file we process.
  -> AbsolutePath
     -- ^ File we process.
  -> MainInterface
  -> Maybe SourceInfo
     -- ^ Optional information about the source code.
  -> TCM (Bool, (Interface, MaybeWarnings))
     -- ^ @Bool@ is: do we have to merge the interface?
getStoredInterface x file isMain msi = do
  -- If something goes wrong (interface outdated etc.)
  -- we revert to fresh type checking.
  let fallback = typeCheck x file isMain msi

  -- Examine the hash of the interface file. If it is different from the
  -- stored version (in stDecodedModules), or if there is no stored version,
  -- read and decode it. Otherwise use the stored version.
  let ifile = filePath $ toIFile file
  h <- fmap snd <$> getInterfaceFileHashes ifile
  mm <- getDecodedModule x
  (cached, mi) <- Bench.billTo [Bench.Deserialization] $ case mm of
    Just mi ->
      if Just (iFullHash mi) /= h
      then do
        dropDecodedModule x
        reportSLn "import.iface" 50 $ "  cached hash = " ++ show (iFullHash mi)
        reportSLn "import.iface" 50 $ "  stored hash = " ++ show h
        reportSLn "import.iface" 5 $ "  file is newer, re-reading " ++ ifile
        (False,) <$> readInterface ifile
      else do
        reportSLn "import.iface" 5 $ "  using stored version of " ++ ifile
        return (True, Just mi)
    Nothing -> do
      reportSLn "import.iface" 5 $ "  no stored version, reading " ++ ifile
      (False,) <$> readInterface ifile

  -- Check that it's the right version
  case mi of
    Nothing       -> do
      reportSLn "import.iface" 5 $ "  bad interface, re-type checking"
      fallback
    Just i        -> do
      reportSLn "import.iface" 5 $ "  imports: " ++ show (iImportedModules i)

      -- We set the pragma options of the skipped file here, so that
      -- we can check that they are compatible with those of the
      -- imported modules. Also, if the top-level file is skipped we
      -- want the pragmas to apply to interactive commands in the UI.
      mapM_ setOptionsFromPragma (iPragmaOptions i)

      -- Check that options that matter haven't changed compared to
      -- current options (issue #2487)
      optionsChanged <-ifM ((not <$> asksTC envCheckOptionConsistency) `or2M`
                            Lens.isBuiltinModule (filePath file))
                       {-then-} (return False) {-else-} $ do
        currentOptions <- useTC stPragmaOptions
        let disagreements =
              [ optName | (opt, optName) <- restartOptions,
                          (opt currentOptions) /= (opt (iOptionsUsed i))]
        if null disagreements then return False else do
          reportSLn "import.iface.options" 4 $ "  Changes in the following options in " ++ prettyShow (filePath file) ++ ", re-typechecking: "  ++ prettyShow disagreements
          return True

      if optionsChanged then fallback else do

        hs <- map iFullHash <$> mapM getInterface (map fst $ iImportedModules i)

        -- If any of the imports are newer we need to retype check
        if hs /= map snd (iImportedModules i)
          then do
            -- liftIO close -- Close the interface file. See above.
            fallback
          else do
            unless cached $ do
              chaseMsg "Loading " x $ Just ifile
              -- print imported warnings
              let ws = filter ((Strict.Just file ==) . tcWarningOrigin) (iWarnings i)
              unless (null ws) $ reportSDoc "warning" 1 $ P.vcat $ P.prettyTCM <$> ws

            return (False, (i, NoWarnings))

-- | Run the type checker on a file and create an interface.
--
--   Mostly, this function calls 'createInterface'.
--   But if it is not the main module we check,
--   we do it in a fresh state, suitably initialize,
--   in order to forget some state changes after successful type checking.

typeCheck
  :: C.TopLevelModuleName
     -- ^ Module name of file we process.
  -> AbsolutePath
     -- ^ File we process.
  -> MainInterface
  -> Maybe SourceInfo
     -- ^ Optional information about the source code.
  -> TCM (Bool, (Interface, MaybeWarnings))
     -- ^ @Bool@ is: do we have to merge the interface?
typeCheck x file isMain msi = do
  unless (includeStateChanges isMain) cleanCachedLog
  let checkMsg = case isMain of
                   MainInterface ScopeCheck -> "Reading "
                   _                        -> "Checking"
      withMsgs = bracket_
       (chaseMsg checkMsg x $ Just $ filePath file)
       (const $ do ws <- getAllWarnings AllWarnings
                   let (we, wa) = classifyWarnings ws
                   let wa' = filter ((Strict.Just file ==) . tcWarningOrigin) wa
                   unless (null wa') $
                     reportSDoc "warning" 1 $ P.vcat $ P.prettyTCM <$> wa'
                   when (null we) $ chaseMsg "Finished" x Nothing)

  -- Do the type checking.

  case isMain of
    MainInterface _ -> do
      r <- withMsgs $ createInterface file x isMain msi
      return (True, r)

    NotMainInterface -> do
      ms       <- getImportPath
      nesting  <- asksTC envModuleNestingLevel
      range    <- asksTC envRange
      call     <- asksTC envCall
      mf       <- useTC stModuleToSource
      vs       <- getVisitedModules
      ds       <- getDecodedModules
      opts     <- stPersistentOptions . stPersistentState <$> getTC
      isig     <- useTC stImports
      ibuiltin <- useTC stImportedBuiltins
      display  <- useTC stImportsDisplayForms
      userwarn <- useTC stImportedUserWarnings
      ipatsyns <- getPatternSynImports
      ho       <- getInteractionOutputCallback
      -- Every interface is treated in isolation. Note: Some changes to
      -- the persistent state may not be preserved if an error other
      -- than a type error or an IO exception is encountered in an
      -- imported module.
      r <- withoutCache $
           -- The cache should not be used for an imported module, and it
           -- should be restored after the module has been type-checked
           freshTCM $
             withImportPath ms $
             localTC (\e -> e { envModuleNestingLevel = nesting
                              -- Andreas, 2014-08-18:
                              -- Preserve the range of import statement
                              -- for reporting termination errors in
                              -- imported modules:
                            , envRange              = range
                            , envCall               = call
                            }) $ do
               setDecodedModules ds
               setCommandLineOptions opts
               setInteractionOutputCallback ho
               stModuleToSource `setTCLens` mf
               setVisitedModules vs
               addImportedThings isig ibuiltin ipatsyns display userwarn []

               r  <- withMsgs $ createInterface file x isMain msi
               mf <- useTC stModuleToSource
               ds <- getDecodedModules
               return (r, do
                  stModuleToSource `setTCLens` mf
                  setDecodedModules ds
                  case r of
                    (i, NoWarnings) -> storeDecodedModule i
                    _               -> return ()
                  )

      case r of
          Left err          -> throwError err
          Right (r, update) -> do
            update
            case r of
              (_, NoWarnings) ->
                -- We skip the file which has just been type-checked to
                -- be able to forget some of the local state from
                -- checking the module.
                -- Note that this doesn't actually read the interface
                -- file, only the cached interface. (This comment is not
                -- correct, see
                -- test/Fail/customised/NestedProjectRoots.err.)
                getStoredInterface x file isMain msi
              _ -> return (False, r)

-- | Formats and outputs the "Checking", "Finished" and "Loading " messages.

chaseMsg
  :: String               -- ^ The prefix, like @Checking@, @Finished@, @Loading @.
  -> C.TopLevelModuleName -- ^ The module name.
  -> Maybe String         -- ^ Optionally: the file name.
  -> TCM ()
chaseMsg kind x file = do
  indentation <- (`replicate` ' ') <$> asksTC envModuleNestingLevel
  let maybeFile = caseMaybe file "." $ \ f -> " (" ++ f ++ ")."
      vLvl | kind == "Checking" = 1
           | otherwise          = 2
  reportSLn "import.chase" vLvl $ concat $
    [ indentation, kind, " ", prettyShow x, maybeFile ]


-- | Print the highlighting information contained in the given interface.

highlightFromInterface
  :: Interface
  -> AbsolutePath
     -- ^ The corresponding file.
  -> TCM ()
highlightFromInterface i file = do
  reportSLn "import.iface" 5 $
    "Generating syntax info for " ++ filePath file ++
    " (read from interface)."
  printHighlightingInfo KeepHighlighting (iHighlighting i)

readInterface :: FilePath -> TCM (Maybe Interface)
readInterface file = do
    -- Decode the interface file
    (s, close) <- liftIO $ readBinaryFile' file
    do  mi <- liftIO . E.evaluate =<< decodeInterface s

        -- Close the file. Note
        -- ⑴ that evaluate ensures that i is evaluated to WHNF (before
        --   the next IO operation is executed), and
        -- ⑵ that decode returns Nothing if an error is encountered,
        -- so it is safe to close the file here.
        liftIO close

        return $ constructIScope <$> mi
      -- Catch exceptions and close
      `catchError` \e -> liftIO close >> handler e
  -- Catch exceptions
  `catchError` handler
  where
    handler e = case e of
      IOException _ _ e -> do
        reportSLn "" 0 $ "IO exception: " ++ show e
        return Nothing   -- Work-around for file locking bug.
                         -- TODO: What does this refer to? Please
                         -- document.
      _ -> throwError e

-- | Writes the given interface to the given file.

writeInterface :: FilePath -> Interface -> TCM ()
writeInterface file i = do
    reportSLn "import.iface.write" 5  $ "Writing interface file " ++ file ++ "."
    -- Andreas, 2015-07-13
    -- After QName memoization (AIM XXI), scope serialization might be cheap enough.
    -- -- Andreas, Makoto, 2014-10-18 AIM XX:
    -- -- iInsideScope is bloating the interface files, so we do not serialize it?
    -- i <- return $
    --   i { iInsideScope  = emptyScopeInfo
    --     }
    -- Andreas, 2016-02-02 this causes issue #1804, so don't do it:
    -- i <- return $
    --   i { iInsideScope  = removePrivates $ iInsideScope i
    --     }
    encodeFile file i
    reportSLn "import.iface.write" 5 $ "Wrote interface file."
    reportSLn "import.iface.write" 50 $ "  hash = " ++ show (iFullHash i) ++ ""
  `catchError` \e -> do
    reportSLn "" 1 $
      "Failed to write interface " ++ file ++ "."
    liftIO $
      whenM (doesFileExist file) $ removeFile file
    throwError e

removePrivates :: ScopeInfo -> ScopeInfo
removePrivates si = si { scopeModules = restrictPrivate <$> scopeModules si }

concreteOptionsToOptionPragmas :: [C.Pragma] -> TCM [OptionsPragma]
concreteOptionsToOptionPragmas p = do
  pragmas <- concat <$> concreteToAbstract_ p
  -- identity for top-level pragmas at the moment
  let getOptions (A.OptionsPragma opts) = Just opts
      getOptions _                      = Nothing
  return $ mapMaybe getOptions pragmas

-- | Tries to type check a module and write out its interface. The
-- function only writes out an interface file if it does not encounter
-- any warnings.
--
-- If appropriate this function writes out syntax highlighting
-- information.

createInterface
  :: AbsolutePath          -- ^ The file to type check.
  -> C.TopLevelModuleName  -- ^ The expected module name.
  -> MainInterface         -- ^ Are we dealing with the main module?
  -> Maybe SourceInfo      -- ^ Optional information about the source code.
  -> TCM (Interface, MaybeWarnings)
createInterface file mname isMain msi =
  Bench.billTo [Bench.TopModule mname] $
  localTC (\e -> e { envCurrentPath = Just file }) $ do

    reportSLn "import.iface.create" 5 $
      "Creating interface for " ++ prettyShow mname ++ "."
    verboseS "import.iface.create" 10 $ do
      visited <- Map.keys <$> getVisitedModules
      reportSLn "import.iface.create" 10 $
        "  visited: " ++ List.intercalate ", " (map prettyShow visited)

    (source, fileType, (pragmas, top)) <- do
      si <- case msi of
        Nothing -> sourceInfo file
        Just si -> return si
      case si of
        SourceInfo {..} -> return (siSource, siFileType, siModule)

    modFile       <- useTC stModuleToSource
    fileTokenInfo <- Bench.billTo [Bench.Highlighting] $
                       generateTokenInfoFromSource
                         file (T.unpack source)
    stTokens `setTCLens` fileTokenInfo

    options <- concreteOptionsToOptionPragmas pragmas
    mapM_ setOptionsFromPragma options


    -- Scope checking.
    reportSLn "import.iface.create" 7 $ "Starting scope checking."
    topLevel <- Bench.billTo [Bench.Scoping] $
      concreteToAbstract_ (TopLevel file mname top)
    reportSLn "import.iface.create" 7 $ "Finished scope checking."

    let ds    = topLevelDecls topLevel
        scope = topLevelScope topLevel

    -- Highlighting from scope checker.
    reportSLn "import.iface.create" 7 $ "Starting highlighting from scope."
    Bench.billTo [Bench.Highlighting] $ do
      -- Generate and print approximate syntax highlighting info.
      ifTopLevelAndHighlightingLevelIs NonInteractive $
        printHighlightingInfo KeepHighlighting fileTokenInfo
      let onlyScope = isMain == MainInterface ScopeCheck
      ifTopLevelAndHighlightingLevelIsOr NonInteractive onlyScope $
        mapM_ (\ d -> generateAndPrintSyntaxInfo d Partial onlyScope) ds
    reportSLn "import.iface.create" 7 $ "Finished highlighting from scope."


    -- Type checking.

    -- Now that all the options are in we can check if caching should
    -- be on.
    activateLoadedFileCache

    -- invalidate cache if pragmas change, TODO move
    cachingStarts
    opts <- useTC stPragmaOptions
    me <- readFromCachedLog
    case me of
      Just (Pragmas opts', _) | opts == opts'
        -> return ()
      _ -> do
        reportSLn "cache" 10 $ "pragma changed: " ++ show (isJust me)
        cleanCachedLog
    writeToCurrentLog $ Pragmas opts

    case isMain of
      MainInterface ScopeCheck -> do
        reportSLn "import.iface.create" 7 $ "Skipping type checking."
        cacheCurrentLog
      _ -> do
        reportSLn "import.iface.create" 7 $ "Starting type checking."
        Bench.billTo [Bench.Typing] $ mapM_ checkDeclCached ds `finally_` cacheCurrentLog
        reportSLn "import.iface.create" 7 $ "Finished type checking."

    -- Ulf, 2013-11-09: Since we're rethrowing the error, leave it up to the
    -- code that handles that error to reset the state.
    -- Ulf, 2013-11-13: Errors are now caught and highlighted in InteractionTop.
    -- catchError_ (checkDecls ds) $ \e -> do
    --   ifTopLevelAndHighlightingLevelIs NonInteractive $
    --     printErrorInfo e
    --   throwError e

    unfreezeMetas

    -- Profiling: Count number of metas.
    verboseS "profile.metas" 10 $ do
      MetaId n <- fresh
      tickN "metas" (fromIntegral n)

    -- Highlighting from type checker.
    reportSLn "import.iface.create" 7 $ "Starting highlighting from type info."
    Bench.billTo [Bench.Highlighting] $ do

      -- Move any remaining token highlighting to stSyntaxInfo.
      toks <- useTC stTokens
      ifTopLevelAndHighlightingLevelIs NonInteractive $
        printHighlightingInfo KeepHighlighting toks
      stTokens `setTCLens` mempty

      -- Grabbing warnings and unsolved metas to highlight them
      warnings <- getAllWarnings AllWarnings
      unless (null warnings) $ reportSDoc "import.iface.create" 20 $
        "collected warnings: " P.<> prettyTCM warnings
      unsolved <- getAllUnsolved
      unless (null unsolved) $ reportSDoc "import.iface.create" 20 $
        "collected unsolved: " P.<> prettyTCM unsolved
      let warningInfo = compress $ foldMap warningHighlighting $ unsolved ++ warnings

      stSyntaxInfo `modifyTCLens` \inf -> (inf `mappend` toks) `mappend` warningInfo

      whenM (optGenerateVimFile <$> commandLineOptions) $
        -- Generate Vim file.
        withScope_ scope $ generateVimFile $ filePath file
    reportSLn "import.iface.create" 7 $ "Finished highlighting from type info."

    setScope scope
    reportSLn "scope.top" 50 $ "SCOPE " ++ show scope

    -- TODO: It would be nice if unsolved things were highlighted
    -- after every mutual block.

    openMetas           <- getOpenMetas
    unless (null openMetas) $ do
      reportSLn "import.metas" 10 "We have unsolved metas."
      reportSLn "import.metas" 10 . unlines =<< showOpenMetas

    ifTopLevelAndHighlightingLevelIs NonInteractive $
      printUnsolvedInfo

    -- Andreas, 2016-08-03, issue #964
    -- When open metas are allowed,
    -- permanently freeze them now by turning them into postulates.
    -- This will enable serialization.
    -- savedMetaStore <- useTC stMetaStore
    allowUnsolved <- optAllowUnsolved <$> pragmaOptions
    unless (includeStateChanges isMain) $
      -- Andreas, 2018-11-15, re issue #3393:
      -- We do not get here when checking the main module
      -- (then includeStateChanges is True).
      when allowUnsolved $ do
        reportSLn "import.iface.create" 7 $ "Turning unsolved metas (if any) into postulates."
        withCurrentModule (scopeCurrent scope) $
          openMetasToPostulates
        -- Clear constraints as they might refer to what
        -- they think are open metas.
        stAwakeConstraints    `setTCLens` []
        stSleepingConstraints `setTCLens` []

    -- Serialization.
    reportSLn "import.iface.create" 7 $ "Starting serialization."
    i <- Bench.billTo [Bench.Serialization, Bench.BuildInterface] $ do
      buildInterface source fileType topLevel options

    reportSLn "tc.top" 101 $ unlines $
      "Signature:" :
      [ unlines
          [ prettyShow x
          , "  type: " ++ show (defType def)
          , "  def:  " ++ show cc
          ]
      | (x, def) <- HMap.toList $ iSignature i ^. sigDefinitions,
        Function{ funCompiled = cc } <- [theDef def]
      ]
    reportSLn "import.iface.create" 7 $ "Finished serialization."

    mallWarnings <- getMaybeWarnings' isMain ErrorWarnings

    reportSLn "import.iface.create" 7 $ "Considering writing to interface file."
    case (mallWarnings, isMain) of
      (SomeWarnings allWarnings, _) -> do
        -- Andreas, 2018-11-15, re issue #3393
        -- The following is not sufficient to fix #3393
        -- since the replacement of metas by postulates did not happen.
        -- -- | not (allowUnsolved && all (isUnsolvedWarning . tcWarning) allWarnings) -> do
        reportSLn "import.iface.create" 7 $ "We have warnings, skipping writing interface file."
        return ()
      (_, MainInterface ScopeCheck) -> do
        reportSLn "import.iface.create" 7 $ "We are just scope-checking, skipping writing interface file."
        return ()
      _ -> Bench.billTo [Bench.Serialization] $ do
        reportSLn "import.iface.create" 7 $ "Actually calling writeInterface."
        -- The file was successfully type-checked (and no warnings were
        -- encountered), so the interface should be written out.
        let ifile = filePath $ toIFile file
        writeInterface ifile i
    reportSLn "import.iface.create" 7 $ "Finished (or skipped) writing to interface file."

    -- -- Restore the open metas, as we might continue in interaction mode.
    -- Actually, we do not serialize the metas if checking the MainInterface
    -- stMetaStore `setTCLens` savedMetaStore

    -- Profiling: Print statistics.
    printStatistics 30 (Just mname) =<< getStatistics

    -- Get the statistics of the current module
    -- and add it to the accumulated statistics.
    localStatistics <- getStatistics
    lensAccumStatistics `modifyTCLens` Map.unionWith (+) localStatistics
    verboseS "profile" 1 $ do
      reportSLn "import.iface" 5 $ "Accumulated statistics."

    return $ first constructIScope (i, mallWarnings)

getUniqueMetasRanges :: [MetaId] -> TCM [Range]
getUniqueMetasRanges = fmap List.nub . mapM getMetaRange

getUnsolvedMetas :: TCM [Range]
getUnsolvedMetas = do
  openMetas            <- getOpenMetas
  interactionMetas     <- getInteractionMetas
  getUniqueMetasRanges (openMetas List.\\ interactionMetas)

getAllUnsolved :: TCM [TCWarning]
getAllUnsolved = do
  unsolvedInteractions <- getUniqueMetasRanges =<< getInteractionMetas
  unsolvedConstraints  <- getAllConstraints
  unsolvedMetas        <- getUnsolvedMetas

  let checkNonEmpty c rs = c rs <$ guard (not $ null rs)

  mapM warning_ $ catMaybes
                [ checkNonEmpty UnsolvedInteractionMetas unsolvedInteractions
                , checkNonEmpty UnsolvedMetaVariables    unsolvedMetas
                , checkNonEmpty UnsolvedConstraints      unsolvedConstraints ]


-- | Collect all warnings that have accumulated in the state.

getAllWarnings :: WhichWarnings -> TCM [TCWarning]
getAllWarnings = getAllWarnings' NotMainInterface

-- | Expert version of 'getAllWarnings'; if 'isMain' is a
-- 'MainInterface', the warnings definitely include also unsolved
-- warnings.

getAllWarnings' :: MainInterface -> WhichWarnings -> TCM [TCWarning]
getAllWarnings' isMain ww = do
  unsolved            <- getAllUnsolved
  collectedTCWarnings <- useTC stTCWarnings

  let showWarn w = classifyWarning w <= ww &&
                    not (null unsolved && onlyShowIfUnsolved w)

  fmap (filter (showWarn . tcWarning))
    $ applyFlagsToTCWarnings' isMain $ reverse
    $ unsolved ++ collectedTCWarnings

getMaybeWarnings :: WhichWarnings -> TCM MaybeWarnings
getMaybeWarnings = getMaybeWarnings' NotMainInterface

getMaybeWarnings' :: MainInterface -> WhichWarnings -> TCM MaybeWarnings
getMaybeWarnings' isMain ww = do
  allWarnings <- getAllWarnings' isMain ww
  return $ if null allWarnings
    -- Andreas, issue 964: not checking null interactionPoints
    -- anymore; we want to serialize with open interaction points now!
           then NoWarnings
           else SomeWarnings allWarnings

getAllWarningsOfTCErr :: TCErr -> TCM [TCWarning]
getAllWarningsOfTCErr err = case err of
  TypeError tcst cls -> case clValue cls of
    NonFatalErrors{} -> return []
    _ -> localTCState $ do
      putTC tcst
      ws <- getAllWarnings AllWarnings
      -- We filter out the unsolved(Metas/Constraints) to stay
      -- true to the previous error messages.
      return $ filter (not . isUnsolvedWarning . tcWarning) ws
  _ -> return []

-- | Reconstruct the 'iScope' (not serialized)
--   from the 'iInsideScope' (serialized).

constructIScope :: Interface -> Interface
constructIScope i = billToPure [ Deserialization ] $
  i{ iScope = publicModules $ iInsideScope i }

-- | Builds an interface for the current module, which should already
-- have been successfully type checked.

buildInterface
  :: Text
     -- ^ Source code.
  -> FileType
     -- ^ Agda file? Literate Agda file?
  -> TopLevelInfo
     -- ^ 'TopLevelInfo' for the current module.
  -> [OptionsPragma]
     -- ^ Options set in @OPTIONS@ pragmas.
  -> TCM Interface
buildInterface source fileType topLevel pragmas = do
    reportSLn "import.iface" 5 "Building interface..."
    let m = topLevelModuleName topLevel
    scope'  <- getScope
    let scope = scope' { scopeCurrent = m }
    -- Andreas, 2014-05-03: killRange did not result in significant reduction
    -- of .agdai file size, and lost a few seconds performance on library-test.
    -- Andreas, Makoto, 2014-10-18 AIM XX: repeating the experiment
    -- with discarding also the nameBindingSite in QName:
    -- Saves 10% on serialization time (and file size)!
    --
    -- NOTE: We no longer discard all nameBindingSites (but the commit
    -- that introduced this change seems to have made Agda a bit
    -- faster and interface file sizes a bit smaller, at least for the
    -- standard library).
    builtin <- useTC stLocalBuiltins
    ms      <- getImports
    mhs     <- mapM (\ m -> (m,) <$> moduleHash m) $ Set.toList ms
    foreignCode <- useTC stForeignCode
    -- Ulf, 2016-04-12:
    -- Non-closed display forms are not applicable outside the module anyway,
    -- and should be dead-code eliminated (#1928).
    display <- HMap.filter (not . null) . HMap.map (filter isClosed) <$> useTC stImportsDisplayForms
    -- TODO: Kill some ranges?
    (display, sig) <- eliminateDeadCode display =<< getSignature
    userwarns  <- useTC stLocalUserWarnings
    importwarn <- useTC stWarningOnImport
    syntaxInfo <- useTC stSyntaxInfo
    optionsUsed <- useTC stPragmaOptions

    -- Andreas, 2015-02-09 kill ranges in pattern synonyms before
    -- serialization to avoid error locations pointing to external files
    -- when expanding a pattern synonym.
    patsyns <- killRange <$> getPatternSyns
    let builtin' = Map.mapWithKey (\ x b -> (x,) . primFunName <$> b) builtin
    warnings <- getAllWarnings AllWarnings
    reportSLn "import.iface" 7 "  instantiating all meta variables"
    i <- instantiateFull $ Interface
      { iSourceHash      = hashText source
      , iSource          = source
      , iFileType        = fileType
      , iImportedModules = mhs
      , iModuleName      = m
      , iScope           = empty -- publicModules scope
      , iInsideScope     = topLevelScope topLevel
      , iSignature       = sig
      , iDisplayForms    = display
      , iUserWarnings    = userwarns
      , iImportWarning   = importwarn
      , iBuiltin         = builtin'
      , iForeignCode     = foreignCode
      , iHighlighting    = syntaxInfo
      , iPragmaOptions   = pragmas
      , iOptionsUsed     = optionsUsed
      , iPatternSyns     = patsyns
      , iWarnings        = warnings
      }
    reportSLn "import.iface" 7 "  interface complete"
    return i

-- | Returns (iSourceHash, iFullHash)
getInterfaceFileHashes :: FilePath -> TCM (Maybe (Hash, Hash))
getInterfaceFileHashes ifile = do
  exist <- liftIO $ doesFileExist ifile
  if not exist then return Nothing else do
    (s, close) <- liftIO $ readBinaryFile' ifile
    let hs = decodeHashes s
    liftIO $ maybe 0 (uncurry (+)) hs `seq` close
    return hs

moduleHash :: ModuleName -> TCM Hash
moduleHash m = iFullHash <$> getInterface m

-- | True if the first file is newer than the second file. If a file doesn't
-- exist it is considered to be infinitely old.
isNewerThan :: FilePath -> FilePath -> IO Bool
isNewerThan new old = do
    newExist <- doesFileExist new
    oldExist <- doesFileExist old
    if not (newExist && oldExist)
        then return newExist
        else do
            newT <- getModificationTime new
            oldT <- getModificationTime old
            return $ newT >= oldT
