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

#if __GLASGOW_HASKELL__ <= 708
import Data.Foldable ( Foldable )
import Data.Traversable ( Traversable, traverse )
#endif

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

import System.Directory (doesFileExist, getModificationTime, removeFile)
import System.FilePath ((</>))

import qualified Text.PrettyPrint.Boxes as Boxes

import Agda.Benchmarking

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Parser
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Internal

import Agda.TypeChecking.Errors
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
import Agda.Interaction.Highlighting.Precise (HighlightingInfo)
import Agda.Interaction.Highlighting.Generate
import Agda.Interaction.Highlighting.Vim

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
    bs <- gets stBuiltinThings
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
    addImportedThings sig bi (iPatternSyns i) (iDisplayForms i) warns
    reportSLn "import.iface.merge" 20 $
      "  Rebinding primitives " ++ show prim
    mapM_ rebind prim
    where
        rebind (x, q) = do
            PrimImpl _ pf <- lookupPrimitiveFunction x
            stImportedBuiltins %= Map.insert x (Prim pf{ primFunName = q })

addImportedThings ::
  Signature -> BuiltinThings PrimFun ->
  A.PatternSynDefns -> DisplayForms -> [TCWarning] -> TCM ()
addImportedThings isig ibuiltin patsyns display warnings = do
  stImports              %= \ imp -> unionSignatures [imp, isig]
  stImportedBuiltins     %= \ imp -> Map.union imp ibuiltin
  stPatternSynImports    %= \ imp -> Map.union imp patsyns
  stImportedDisplayForms %= \ imp -> HMap.unionWith (++) imp display
  stTCWarnings           %= \ imp -> List.union imp warnings
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
    -- let s = publicModules $ iInsideScope i
    let s = iScope i
    return (iModuleName i `withRangesOfQ` mnameToConcrete x, s)

data MaybeWarnings' a = NoWarnings | SomeWarnings a
  deriving (Functor, Foldable, Traversable)
type MaybeWarnings = MaybeWarnings' [TCWarning]

applyFlagsToMaybeWarnings :: IgnoreFlags -> MaybeWarnings -> TCM MaybeWarnings
applyFlagsToMaybeWarnings r mw = do
  w' <- traverse (applyFlagsToTCWarnings r) mw
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
                  TCM (Interface, MaybeWarnings) ->
                  TCM (Interface, MaybeWarnings)
alreadyVisited x isMain getIface = do
    mm <- getVisitedModule x
    case mm of
        -- A module with warnings should never be allowed to be
        -- imported from another module.
        Just mi | not (miWarnings mi) -> do
          reportSLn "import.visit" 10 $ "  Already visited " ++ prettyShow x
          return (miInterface mi, NoWarnings)
        _ -> do
          reportSLn "import.visit" 5 $ "  Getting interface for " ++ prettyShow x
          r@(i, wt) <- getIface
          reportSLn "import.visit" 5 $ "  Now we've looked at " ++ prettyShow x
          unless (isMain == MainInterface ScopeCheck) $
            visitModule $ ModuleInfo
              { miInterface  = i
              , miWarnings   = hasWarnings wt
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

typeCheckMain :: AbsolutePath -> Mode -> TCM (Interface, MaybeWarnings)
typeCheckMain f mode = do
  -- liftIO $ putStrLn $ "This is typeCheckMain " ++ prettyShow f
  -- liftIO . putStrLn . show =<< getVerbosity
  reportSLn "import.main" 10 $ "Importing the primitive modules."
  libdir <- liftIO defaultLibDir
  reportSLn "import.main" 20 $ "Library dir = " ++ show libdir
  -- To allow posulating the built-ins, check the primitive module
  -- in unsafe mode
  _ <- bracket_ (gets $ Lens.getSafeMode) Lens.putSafeMode $ do
    Lens.putSafeMode False
    -- Turn off import-chasing messages.
    -- We have to modify the persistent verbosity setting, since
    -- getInterface resets the current verbosity settings to the persistent ones.
    bracket_ (gets $ Lens.getPersistentVerbosity) Lens.putPersistentVerbosity $ do
      Lens.modifyPersistentVerbosity (Trie.delete [])  -- set root verbosity to 0
      -- We don't want to generate highlighting information for Agda.Primitive.
      withHighlightingLevel None $
        getInterface_ =<< do
          moduleName $ mkAbsolute $
            libdir </> "prim" </> "Agda" </> "Primitive.agda"
  reportSLn "import.main" 10 $ "Done importing the primitive modules."

  -- Now do the type checking via getInterface.
  m <- moduleName f
  getInterface' m (MainInterface mode)

-- | Tries to return the interface associated to the given (imported) module.
--   The time stamp of the relevant interface file is also returned.
--   Calls itself recursively for the imports of the given module.
--   May type check the module.
--   An error is raised if a warning is encountered.
--
--   Do not use this for the main file, use 'typeCheckMain' instead.

getInterface :: ModuleName -> TCM Interface
getInterface = getInterface_ . toTopLevelModuleName

-- | See 'getInterface'.

getInterface_ :: C.TopLevelModuleName -> TCM Interface
getInterface_ x = do
  (i, wt) <- getInterface' x NotMainInterface
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
  -> TCM (Interface, MaybeWarnings)
getInterface' x isMain = do
  withIncreasedModuleNestingLevel $ do
    -- Preserve the pragma options unless we are checking the main
    -- interface.
    bracket_ (use stPragmaOptions)
             (unless (includeStateChanges isMain) . setPragmaOptions) $ do
     -- Forget the pragma options (locally).
     setCommandLineOptions . stPersistentOptions . stPersistentState =<< get

     alreadyVisited x isMain $ addImportCycleCheck x $ do
      file <- findFile x  -- requires source to exist

      reportSLn "import.iface" 10 $ "  Check for cycle"
      checkForImportCycle

      uptodate <- Bench.billTo [Bench.Import] $ do
        ignore <- ignoreInterfaces
        cached <- runMaybeT $ isCached x file
          -- If it's cached ignoreInterfaces has no effect;
          -- to avoid typechecking a file more than once.
        sourceH <- liftIO $ hashFile file
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
          then getStoredInterface x file isMain
          else typeCheck          x file isMain

      -- Ensure that the given module name matches the one in the file.
      let topLevelName = toTopLevelModuleName $ iModuleName i
      unless (topLevelName == x) $ do
        -- Andreas, 2014-03-27 This check is now done in the scope checker.
        -- checkModuleName topLevelName file
        typeError $ OverlappingProjects file topLevelName x

      visited <- isVisited x
      reportSLn "import.iface" 5 $ if visited then "  We've been here. Don't merge."
                                   else "  New module. Let's check it out."
      unless (visited || stateChangesIncluded) $ do
        mergeInterface i
        Bench.billTo [Bench.Highlighting] $
          ifTopLevelAndHighlightingLevelIs NonInteractive $
            highlightFromInterface i file

      stCurrentModule .= Just (iModuleName i)

      -- Interfaces are not stored if we are only scope-checking, or
      -- if any warnings were encountered.
      case (isMain, wt) of
        (MainInterface ScopeCheck, _) -> return ()
        (_, SomeWarnings w)           -> return ()
        _                             -> storeDecodedModule i

      return (i, wt)

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
  -> TCM (Bool, (Interface, MaybeWarnings))
     -- ^ @Bool@ is: do we have to merge the interface?
getStoredInterface x file isMain = do
  -- If something goes wrong (interface outdated etc.)
  -- we revert to fresh type checking.
  let fallback = typeCheck x file isMain

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

          -- We set the pragma options of the skipped file here,
          -- because if the top-level file is skipped we want the
          -- pragmas to apply to interactive commands in the UI.
          mapM_ setOptionsFromPragma (iPragmaOptions i)
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
  -> TCM (Bool, (Interface, MaybeWarnings))
     -- ^ @Bool@ is: do we have to merge the interface?
typeCheck x file isMain = do
  unless (includeStateChanges isMain) cleanCachedLog
  let checkMsg = case isMain of
                   MainInterface ScopeCheck -> "Reading "
                   _                        -> "Checking"
      withMsgs = bracket_
       (chaseMsg checkMsg x $ Just $ filePath file)
       (const $ do ws <- getAllWarnings' AllWarnings RespectFlags
                   let (we, wa) = classifyWarnings ws
                   let wa' = filter ((Strict.Just file ==) . tcWarningOrigin) wa
                   unless (null wa') $
                     reportSDoc "warning" 1 $ P.vcat $ P.prettyTCM <$> wa'
                   when (null we) $ chaseMsg "Finished" x Nothing)

  -- Do the type checking.

  case isMain of
    MainInterface _ -> do
      r <- withMsgs $ createInterface file x isMain

      -- Merge the signature with the signature for imported
      -- things.
      reportSLn "import.iface" 40 $ "Merging with state changes included."
      sig     <- getSignature
      patsyns <- getPatternSyns
      display <- use stImportsDisplayForms
      addImportedThings sig Map.empty patsyns display []
      setSignature emptySignature
      setPatternSyns Map.empty

      return (True, r)
    NotMainInterface -> do
      ms       <- getImportPath
      nesting  <- asks envModuleNestingLevel
      range    <- asks envRange
      call     <- asks envCall
      mf       <- use stModuleToSource
      vs       <- getVisitedModules
      ds       <- getDecodedModules
      opts     <- stPersistentOptions . stPersistentState <$> get
      isig     <- use stImports
      ibuiltin <- use stImportedBuiltins
      display  <- use stImportsDisplayForms
      ipatsyns <- getPatternSynImports
      ho       <- getInteractionOutputCallback
      -- Every interface is treated in isolation. Note: Some changes to
      -- the persistent state may not be preserved if an error other
      -- than a type error or an IO exception is encountered in an
      -- imported module.
      r <- noCacheForImportedModule $
           freshTCM $
             withImportPath ms $
             local (\e -> e { envModuleNestingLevel = nesting
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
               stModuleToSource .= mf
               setVisitedModules vs
               addImportedThings isig ibuiltin ipatsyns display []

               r  <- withMsgs $ createInterface file x isMain
               mf <- use stModuleToSource
               ds <- getDecodedModules
               return (r, do
                  stModuleToSource .= mf
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
                getStoredInterface x file isMain
              _ -> return (False, r)

-- | Formats and outputs the "Checking", "Finished" and "Loading " messages.

chaseMsg
  :: String               -- ^ The prefix, like @Checking@, @Finished@, @Loading @.
  -> C.TopLevelModuleName -- ^ The module name.
  -> Maybe String         -- ^ Optionally: the file name.
  -> TCM ()
chaseMsg kind x file = do
  indentation <- (`replicate` ' ') <$> asks envModuleNestingLevel
  let maybeFile = caseMaybe file "." $ \ f -> " (" ++ f ++ ")."
  reportSLn "import.chase" 1 $ concat $
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
  printHighlightingInfo (iHighlighting i)


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

-- | Tries to type check a module and write out its interface. The
-- function only writes out an interface file if it does not encounter
-- any warnings.
--
-- If appropriate this function writes out syntax highlighting
-- information.

createInterface
  :: AbsolutePath          -- ^ The file to type check.
  -> C.TopLevelModuleName  -- ^ The expected module name.
  -> MainInterface
  -> TCM (Interface, MaybeWarnings)
createInterface file mname isMain = Bench.billTo [Bench.TopModule mname] $
  local (\e -> e { envCurrentPath = Just file }) $ do
    modFile       <- use stModuleToSource
    fileTokenInfo <- Bench.billTo [Bench.Highlighting] $
                       generateTokenInfo file
    stTokens .= fileTokenInfo

    reportSLn "import.iface.create" 5 $
      "Creating interface for " ++ prettyShow mname ++ "."
    verboseS "import.iface.create" 10 $ do
      visited <- Map.keys <$> getVisitedModules
      reportSLn "import.iface.create" 10 $
        "  visited: " ++ List.intercalate ", " (map prettyShow visited)

    -- Parsing.
    (pragmas, top) <- Bench.billTo [Bench.Parsing] $
      runPM $ parseFile' moduleParser file

    pragmas <- concat <$> concreteToAbstract_ pragmas
               -- identity for top-level pragmas at the moment
    let getOptions (A.OptionsPragma opts) = Just opts
        getOptions _                      = Nothing
        options = catMaybes $ map getOptions pragmas
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
        printHighlightingInfo fileTokenInfo
      let onlyScope = isMain == MainInterface ScopeCheck
      ifTopLevelAndHighlightingLevelIsOr NonInteractive onlyScope $
        mapM_ (\ d -> generateAndPrintSyntaxInfo d Partial onlyScope) ds
    reportSLn "import.iface.create" 7 $ "Finished highlighting from scope."


    -- Type checking.

    -- invalidate cache if pragmas change, TODO move
    cachingStarts
    opts <- use stPragmaOptions
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
      toks <- use stTokens
      ifTopLevelAndHighlightingLevelIs NonInteractive $ printHighlightingInfo toks
      stTokens .= mempty
      stSyntaxInfo %= \inf -> inf `mappend` toks

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
    -- savedMetaStore <- use stMetaStore
    unless (includeStateChanges isMain) $
      whenM (optAllowUnsolved <$> pragmaOptions) $ do
        withCurrentModule (scopeCurrent scope) $
          openMetasToPostulates
        -- Clear constraints as they might refer to what
        -- they think are open metas.
        stAwakeConstraints    .= []
        stSleepingConstraints .= []

    -- Serialization.
    reportSLn "import.iface.create" 7 $ "Starting serialization."
    syntaxInfo <- use stSyntaxInfo
    i <- Bench.billTo [Bench.Serialization, Bench.BuildInterface] $ do
      buildInterface file topLevel syntaxInfo options

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

    mallWarnings <- getAllWarnings ErrorWarnings
                      $ case isMain of
                          MainInterface _  -> IgnoreFlags
                          NotMainInterface -> RespectFlags

    reportSLn "import.iface.create" 7 $ "Considering writing to interface file."
    case (mallWarnings, isMain) of
      (SomeWarnings allWarnings, _) -> return ()
      (_, MainInterface ScopeCheck) -> return ()
      _ -> Bench.billTo [Bench.Serialization] $ do
        -- The file was successfully type-checked (and no warnings were
        -- encountered), so the interface should be written out.
        let ifile = filePath $ toIFile file
        writeInterface ifile i
    reportSLn "import.iface.create" 7 $ "Finished (or skipped) writing to interface file."

    -- -- Restore the open metas, as we might continue in interaction mode.
    -- Actually, we do not serialize the metas if checking the MainInterface
    -- stMetaStore .= savedMetaStore

    -- Profiling: Print statistics.
    printStatistics 30 (Just mname) =<< getStatistics

    -- Get the statistics of the current module
    -- and add it to the accumulated statistics.
    localStatistics <- getStatistics
    lensAccumStatistics %= Map.unionWith (+) localStatistics
    verboseS "profile" 1 $ do
      reportSLn "import.iface" 5 $ "Accumulated statistics."

    return $ first constructIScope (i, mallWarnings)

-- | Collect all warnings that have accumulated in the state.
-- Depending on the argument, we either respect the flags passed
-- in by the user, or not (for instance when deciding if we are
-- writing an interface file or not)

getAllWarnings' :: WhichWarnings -> IgnoreFlags -> TCM [TCWarning]
getAllWarnings' ww ifs = do
  openMetas            <- getOpenMetas
  interactionMetas     <- getInteractionMetas
  let getUniqueMetas = fmap List.nub . mapM getMetaRange
  unsolvedInteractions <- getUniqueMetas interactionMetas
  unsolvedMetas        <- getUniqueMetas (openMetas List.\\ interactionMetas)
  unsolvedConstraints  <- getAllConstraints
  collectedTCWarnings  <- use stTCWarnings

  unsolved <- mapM warning_
                   [ UnsolvedInteractionMetas unsolvedInteractions
                   , UnsolvedMetaVariables    unsolvedMetas
                   , UnsolvedConstraints      unsolvedConstraints ]

  fmap (filter ((<= ww) . classifyWarning . tcWarning))
    $ applyFlagsToTCWarnings ifs $ reverse
    $ unsolved ++ collectedTCWarnings

getAllWarnings :: WhichWarnings -> IgnoreFlags -> TCM MaybeWarnings
getAllWarnings ww ifs = do
  allWarnings <- getAllWarnings' ww ifs
  return $ if null allWarnings
    -- Andreas, issue 964: not checking null interactionPoints
    -- anymore; we want to serialize with open interaction points now!
           then NoWarnings
           else SomeWarnings allWarnings

errorWarningsOfTCErr :: TCErr -> TCM [TCWarning]
errorWarningsOfTCErr err = case err of
  TypeError tcst cls -> case clValue cls of
    NonFatalErrors{} -> return []
    _ -> localState $ do
      put tcst
      ws <- getAllWarnings' ErrorWarnings RespectFlags
      -- We filter out the unsolved(Metas/Constraints) to stay
      -- true to the previous error messages.
      return $ filter (not . isUnsolvedWarning . tcWarning) ws
  _ -> return []

-- constructIScope :: ScopeInfo -> Map ModuleName Scope
constructIScope :: Interface -> Interface
constructIScope i = i{ iScope = billToPure [ Deserialization ] $ publicModules $ iInsideScope i }

-- | Builds an interface for the current module, which should already
-- have been successfully type checked.

buildInterface
  :: AbsolutePath
  -> TopLevelInfo
     -- ^ 'TopLevelInfo' for the current module.
  -> HighlightingInfo
     -- ^ Syntax highlighting info for the module.
  -> [OptionsPragma]
     -- ^ Options set in @OPTIONS@ pragmas.
  -> TCM Interface
buildInterface file topLevel syntaxInfo pragmas = do
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
    builtin <- use stLocalBuiltins
    ms      <- getImports
    mhs     <- mapM (\ m -> (m,) <$> moduleHash m) $ Set.toList ms
    foreignCode <- use stForeignCode
    -- Ulf, 2016-04-12:
    -- Non-closed display forms are not applicable outside the module anyway,
    -- and should be dead-code eliminated (#1928).
    display <- HMap.filter (not . null) . HMap.map (filter isGlobal) <$> use stImportsDisplayForms
    -- TODO: Kill some ranges?
    (display, sig) <- eliminateDeadCode display =<< getSignature
    -- Andreas, 2015-02-09 kill ranges in pattern synonyms before
    -- serialization to avoid error locations pointing to external files
    -- when expanding a pattern synoym.
    patsyns <- killRange <$> getPatternSyns
    h       <- liftIO $ hashFile file
    let builtin' = Map.mapWithKey (\ x b -> (x,) . primFunName <$> b) builtin
    warnings <- getAllWarnings' AllWarnings RespectFlags
    reportSLn "import.iface" 7 "  instantiating all meta variables"
    i <- instantiateFull $ Interface
      { iSourceHash      = h
      , iImportedModules = mhs
      , iModuleName      = m
      , iScope           = empty -- publicModules scope
      , iInsideScope     = topLevelScope topLevel
      , iSignature       = sig
      , iDisplayForms    = display
      , iBuiltin         = builtin'
      , iForeignCode     = foreignCode
      , iHighlighting    = syntaxInfo
      , iPragmaOptions   = pragmas
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
