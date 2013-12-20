{-# LANGUAGE CPP #-}
{-| This module deals with finding imported modules and loading their
    interface files.
-}
module Agda.Interaction.Imports where

import Prelude

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import qualified Control.Exception as E

import Data.Function (on)
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Foldable as Fold (toList)
import Data.List
import Data.Maybe
import Data.Monoid (mempty, mappend)
import Data.Map (Map)
import Data.Set (Set)
import System.Directory (doesFileExist, getModificationTime, removeFile)
import System.FilePath ((</>))

import Paths_Agda (getDataFileName)

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Parser
import Agda.Syntax.Scope.Base
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Internal

import Agda.TypeChecking.Errors
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Serialise
import Agda.TypeChecking.Primitive
import Agda.TypeChecker

import Agda.Interaction.FindFile
import Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens
import Agda.Interaction.Highlighting.Precise (HighlightingInfo)
import Agda.Interaction.Highlighting.Generate
import Agda.Interaction.Highlighting.Vim

import Agda.Utils.FileName
import Agda.Utils.Monad
import Agda.Utils.IO.Binary
import Agda.Utils.Pretty
import Agda.Utils.Fresh
import Agda.Utils.Time
import Agda.Utils.Hash
import qualified Agda.Utils.Trie as Trie

#include "../undefined.h"
import Agda.Utils.Impossible

-- | Merge an interface into the current proof state.
mergeInterface :: Interface -> TCM ()
mergeInterface i = do
    let sig	= iSignature i
	builtin = Map.toList $ iBuiltin i
	prim	= [ x | (_,Prim x) <- builtin ]
	bi	= Map.fromList [ (x,Builtin t) | (x,Builtin t) <- builtin ]
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
    addImportedThings sig bi (iHaskellImports i) (iPatternSyns i)
    reportSLn "import.iface.merge" 20 $
      "  Rebinding primitives " ++ show prim
    prim <- Map.fromList <$> mapM rebind prim
    modify $ \st -> st { stImportedBuiltins = stImportedBuiltins st `Map.union` prim
		       }
    where
	rebind (x, q) = do
	    PrimImpl _ pf <- lookupPrimitiveFunction x
	    return (x, Prim $ pf { primFunName = q })

addImportedThings ::
  Signature -> BuiltinThings PrimFun -> Set String -> A.PatternSynDefns -> TCM ()
addImportedThings isig ibuiltin hsImports patsyns =
  modify $ \st -> st
    { stImports          = unionSignatures [stImports st, isig]
    , stImportedBuiltins = Map.union (stImportedBuiltins st) ibuiltin
    , stHaskellImports   = Set.union (stHaskellImports st) hsImports
    , stPatternSynImports = Map.union (stPatternSynImports st) patsyns
    }

-- | Scope checks the given module. A proper version of the module
-- name (with correct definition sites) is returned.

scopeCheckImport :: ModuleName -> TCM (ModuleName, Map ModuleName Scope)
scopeCheckImport x = do
    reportSLn "import.scope" 5 $ "Scope checking " ++ show x
    verboseS "import.scope" 10 $ do
      visited <- Map.keys <$> getVisitedModules
      reportSLn "import.scope" 10 $
        "  visited: " ++ intercalate ", " (map (render . pretty) visited)
    i <- getInterface x
    addImport x
    return (iModuleName i `withRangesOfQ` mnameToConcrete x, iScope i)

data MaybeWarnings = NoWarnings | SomeWarnings Warnings

hasWarnings :: MaybeWarnings -> Bool
hasWarnings NoWarnings     = False
hasWarnings SomeWarnings{} = True

-- | If the module has already been visited (without warnings), then
-- its interface is returned directly. Otherwise the computation is
-- used to find the interface and the computed interface is stored for
-- potential later use.

alreadyVisited :: C.TopLevelModuleName ->
                  TCM (Interface, MaybeWarnings) ->
                  TCM (Interface, MaybeWarnings)
alreadyVisited x getIface = do
    mm <- getVisitedModule x
    case mm of
        -- A module with warnings should never be allowed to be
        -- imported from another module.
	Just mi | not (miWarnings mi) -> do
          reportSLn "import.visit" 10 $ "  Already visited " ++ render (pretty x)
          return (miInterface mi, NoWarnings)
	_ -> do
          reportSLn "import.visit" 5 $ "  Getting interface for " ++ render (pretty x)
          r@(i, wt) <- getIface
          reportSLn "import.visit" 5 $ "  Now we've looked at " ++ render (pretty x)
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
--   Then, 'typeCheck' is called to do the main work.

typeCheckMain :: AbsolutePath -> TCM (Interface, MaybeWarnings)
typeCheckMain f = do
  -- liftIO $ putStrLn $ "This is typeCheckMain " ++ show f
  -- liftIO . putStrLn . show =<< getVerbosity
  reportSLn "import.main" 10 $ "Importing the primitive modules."
  libpath <- liftIO $ getDataFileName "lib"
  reportSLn "import.main" 20 $ "Library path = " ++ show libpath
  -- To allow posulating the built-ins, check the primitive module
  -- in unsafe mode
  bracket_ (gets $ Lens.getSafeMode) Lens.putSafeMode $ do
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
            libpath </> "prim" </> "Agda" </> "Primitive.agda"
  reportSLn "import.main" 10 $ "Done importing the primitive modules."
  typeCheck f

-- | Type checks the given module (if necessary).
--
--   Called recursively for imported modules.

typeCheck :: AbsolutePath -> TCM (Interface, MaybeWarnings)
typeCheck f = do
  m <- moduleName f
  getInterface' m True

-- | Tries to return the interface associated to the given module. The
-- time stamp of the relevant interface file is also returned. May
-- type check the module. An error is raised if a warning is
-- encountered.

getInterface :: ModuleName -> TCM Interface
getInterface = getInterface_ . toTopLevelModuleName

getInterface_ :: C.TopLevelModuleName -> TCM Interface
getInterface_ x = do
  (i, wt) <- getInterface' x False
  case wt of
    SomeWarnings w  -> typeError $ warningsToError w
    NoWarnings      -> return i

-- | A more precise variant of 'getInterface'. If warnings are
-- encountered then they are returned instead of being turned into
-- errors.

getInterface' :: C.TopLevelModuleName
              -> Bool  -- ^ If type checking is necessary, should all
                       -- state changes inflicted by 'createInterface'
                       -- be preserved?
              -> TCM (Interface, MaybeWarnings)
getInterface' x includeStateChanges =
  withIncreasedModuleNestingLevel $
  -- Preserve the pragma options unless includeStateChanges is True.
  bracket_ (stPragmaOptions <$> get)
           (unless includeStateChanges . setPragmaOptions) $ do
   -- Forget the pragma options (locally).
   setCommandLineOptions . stPersistentOptions . stPersistent =<< get

   alreadyVisited x $ addImportCycleCheck x $ do
    file <- findFile x  -- requires source to exist

    reportSLn "import.iface" 10 $ "  Check for cycle"
    checkForImportCycle

    uptodate <- do
      ignore <- ignoreInterfaces
      cached <- isCached file -- if it's cached ignoreInterfaces has no effect
                              -- to avoid typechecking a file more than once
      sourceH <- liftIO $ hashFile file
      ifaceH  <-
        case cached of
          Nothing -> fmap fst <$> getInterfaceFileHashes (filePath $ toIFile file)
          Just i  -> return $ Just $ iSourceHash i
      let unchanged = Just sourceH == ifaceH
      return $ unchanged && (not ignore || isJust cached)

    reportSLn "import.iface" 5 $
      "  " ++ render (pretty x) ++ " is " ++
      (if uptodate then "" else "not ") ++ "up-to-date."

    (stateChangesIncluded, (i, wt)) <-
      if uptodate then skip file else typeCheck file

    -- Ensure that the given module name matches the one in the file.
    let topLevelName = toTopLevelModuleName $ iModuleName i
    unless (topLevelName == x) $ do
      checkModuleName topLevelName file
      typeError $ OverlappingProjects file topLevelName x

    visited <- isVisited x
    reportSLn "import.iface" 5 $ if visited then "  We've been here. Don't merge."
                                 else "  New module. Let's check it out."
    unless (visited || stateChangesIncluded) $ do
      mergeInterface i
      ifTopLevelAndHighlightingLevelIs NonInteractive $
        highlightFromInterface i file

    modify (\s -> s { stCurrentModule = Just $ iModuleName i })

    -- Interfaces are only stored if no warnings were encountered.
    case wt of
      SomeWarnings w -> return ()
      NoWarnings     -> storeDecodedModule i

    return (i, wt)

    where
      isCached file = do
        let ifile = filePath $ toIFile file
        exist <- liftIO $ doesFileExistCaseSensitive ifile
        if not exist
          then return Nothing
          else do
            h  <- fmap snd <$> getInterfaceFileHashes ifile
            mm <- getDecodedModule x
            return $ case mm of
              Just mi | Just (iFullHash mi) == h -> Just mi
              _                                  -> Nothing

      -- Formats the "Checking", "Finished" and "Skipping" messages.
      chaseMsg kind file = do
        nesting <- envModuleNestingLevel <$> ask
        let s = genericReplicate nesting ' ' ++ kind ++
                " " ++ render (pretty x) ++
                case file of
                  Nothing -> "."
                  Just f  -> " (" ++ f ++ ")."
        reportSLn "import.chase" 1 s

      skip file = do
        -- Examine the hash of the interface file. If it is different from the
        -- stored version (in stDecodedModules), or if there is no stored version,
        -- read and decode it. Otherwise use the stored version.
        let ifile = filePath $ toIFile file
        h <- fmap snd <$> getInterfaceFileHashes ifile
        mm <- getDecodedModule x
        (cached, mi) <- case mm of
          Just mi ->
            if Just (iFullHash mi) /= h
            then do dropDecodedModule x
                    reportSLn "import.iface" 50 $ "  cached hash = " ++ show (iFullHash mi)
                    reportSLn "import.iface" 50 $ "  stored hash = " ++ show h
                    reportSLn "import.iface" 5 $ "  file is newer, re-reading " ++ ifile
                    (,) False <$> readInterface ifile
            else do reportSLn "import.iface" 5 $ "  using stored version of " ++ ifile
                    return (True, Just mi)
          Nothing -> do
            reportSLn "import.iface" 5 $ "  no stored version, reading " ++ ifile
            (,) False <$> readInterface ifile

        -- Check that it's the right version
        case mi of
          Nothing	-> do
            reportSLn "import.iface" 5 $ "  bad interface, re-type checking"
            typeCheck file
          Just i	-> do

            reportSLn "import.iface" 5 $ "  imports: " ++ show (iImportedModules i)

            hs <- map iFullHash <$> mapM getInterface (map fst $ iImportedModules i)

            -- If any of the imports are newer we need to retype check
            if hs /= map snd (iImportedModules i)
              then do
                -- liftIO close	-- Close the interface file. See above.
                typeCheck file
              else do
                unless cached $ chaseMsg "Skipping" (Just ifile)
                -- We set the pragma options of the skipped file here,
                -- because if the top-level file is skipped we want the
                -- pragmas to apply to interactive commands in the UI.
                mapM_ setOptionsFromPragma (iPragmaOptions i)
                return (False, (i, NoWarnings))

      typeCheck file = do
          let withMsgs m = do
                chaseMsg "Checking" (Just $ filePath file)
                x <- m
                chaseMsg "Finished" Nothing
                return x

          -- Do the type checking.

          if includeStateChanges then do
            r <- withMsgs $ createInterface file x

            -- Merge the signature with the signature for imported
            -- things.
            sig <- getSignature
            patsyns <- getPatternSyns
            addImportedThings sig Map.empty Set.empty patsyns
            setSignature emptySignature
            setPatternSyns Map.empty

            return (True, r)
           else do
            ms       <- getImportPath
            emacs    <- envEmacs <$> ask
            nesting  <- envModuleNestingLevel <$> ask
            mf       <- stModuleToSource <$> get
            vs       <- getVisitedModules
            ds       <- getDecodedModules
            opts     <- stPersistentOptions . stPersistent <$> get
            isig     <- getImportedSignature
            ibuiltin <- gets stImportedBuiltins
            ipatsyns <- getPatternSynImports
            ho       <- getInteractionOutputCallback
            -- Every interface is treated in isolation. Note: Changes
            -- to stDecodedModules are not preserved if an error is
            -- encountered in an imported module.
            r <- liftIO $ runTCM $
                   withImportPath ms $
                   local (\e -> e { envEmacs              = emacs
                                  , envModuleNestingLevel = nesting
                                  }) $ do
                     setDecodedModules ds
                     setCommandLineOptions opts
                     setInteractionOutputCallback ho
                     modify $ \s -> s { stModuleToSource     = mf
                                      }
                     setVisitedModules vs
                     addImportedThings isig ibuiltin Set.empty ipatsyns

                     r  <- withMsgs $ createInterface file x
                     mf <- stModuleToSource <$> get
                     ds <- getDecodedModules
                     return (r, do
                        modify $ \s -> s { stModuleToSource = mf }
                        setDecodedModules ds
                        case r of
                          (i, NoWarnings) -> storeDecodedModule i
                          _               -> return ()
                        )

            case r of
                Left err               -> throwError err
                Right (r, update) -> do
                  update
                  case r of
                    (_, NoWarnings) ->
                      -- We skip the file which has just been type-checked to
                      -- be able to forget some of the local state from
                      -- checking the module.
                      -- Note that this doesn't actually read the interface
                      -- file, only the cached interface.
                      skip file
                    _ -> return (False, r)

-- | Print the highlighting information contained in the given
-- interface.

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
    do  i <- liftIO . E.evaluate =<< decodeInterface s

        -- Close the file. Note
        -- ⑴ that evaluate ensures that i is evaluated to WHNF (before
        --   the next IO operation is executed), and
        -- ⑵ that decode returns Nothing if an error is encountered,
        -- so it is safe to close the file here.
        liftIO close

        return i
      -- Catch exceptions and close
      `catchError` \e -> liftIO close >> handler e
  -- Catch exceptions
  `catchError` handler
  where
    handler e = case e of
      IOException _ e -> do
        reportSLn "" 0 $ "IO exception: " ++ show e
        return Nothing   -- Work-around for file locking bug.
                         -- TODO: What does this refer to? Please
                         -- document.
      _               -> throwError e

-- | Writes the given interface to the given file. Returns the file's
-- new modification time stamp, or 'Nothing' if the write failed.

writeInterface :: FilePath -> Interface -> TCM ()
writeInterface file i = do
    reportSLn "import.iface.write" 5  $ "Writing interface file " ++ file ++ "."
    encodeFile file i
    reportSLn "import.iface.write" 5 $ "Wrote interface file."
    reportSLn "import.iface.write" 50 $ "  hash = " ++ show (iFullHash i) ++ ""
  `catchError` \e -> do
    reportSLn "" 1 $
      "Failed to write interface " ++ file ++ "."
    liftIO $
      whenM (doesFileExist file) $ removeFile file
    throwError e

-- | Tries to type check a module and write out its interface. The
-- function only writes out an interface file if it does not encounter
-- any warnings.
--
-- If appropriate this function writes out syntax highlighting
-- information.

createInterface
  :: AbsolutePath          -- ^ The file to type check.
  -> C.TopLevelModuleName  -- ^ The expected module name.
  -> TCM (Interface, MaybeWarnings)
createInterface file mname =
  local (\e -> e { envCurrentPath = file }) $ do
    modFile       <- stModuleToSource <$> get
    fileTokenInfo <- generateTokenInfo file
    modify $ \st -> st { stTokens = fileTokenInfo }

    reportSLn "import.iface.create" 5 $
      "Creating interface for " ++ render (pretty mname) ++ "."
    verboseS "import.iface.create" 10 $ do
      visited <- Map.keys <$> getVisitedModules
      reportSLn "import.iface.create" 10 $
        "  visited: " ++ intercalate ", " (map (render . pretty) visited)

    previousHsImports <- getHaskellImports

    (pragmas, top) <- liftIO $ parseFile' moduleParser file

    pragmas <- concat <$> concreteToAbstract_ pragmas
               -- identity for top-level pragmas at the moment
    let getOptions (A.OptionsPragma opts) = Just opts
        getOptions _                      = Nothing
        options = catMaybes $ map getOptions pragmas
    mapM_ setOptionsFromPragma options
    topLevel <- concreteToAbstract_ (TopLevel file top)

    let ds = topLevelDecls topLevel

    ifTopLevelAndHighlightingLevelIs NonInteractive $ do
      -- Generate and print approximate syntax highlighting info.
      printHighlightingInfo fileTokenInfo
      mapM_ (\d -> generateAndPrintSyntaxInfo d Partial) ds

    checkDecls ds
    -- Ulf, 2013-11-09: Since we're rethrowing the error, leave it up to the
    -- code that handles that error to reset the state.
    -- Ulf, 2013-11-13: Errors are now caught and highlighted in InteractionTop.
    -- catchError_ (checkDecls ds) $ \e -> do
    --   ifTopLevelAndHighlightingLevelIs NonInteractive $
    --     printErrorInfo e
    --   throwError e

    unfreezeMetas

    -- Count number of metas
    verboseS "profile.metas" 10 $ do
      MetaId n <- fresh
      tickN "metas" (fromIntegral n)

    -- Move any remaining token highlighting to stSyntaxInfo.
    ifTopLevelAndHighlightingLevelIs NonInteractive $
      printHighlightingInfo . stTokens =<< get
    modify $ \st ->
      st { stTokens     = mempty
         , stSyntaxInfo = stSyntaxInfo st `mappend` stTokens st
         }

    whenM (optGenerateVimFile <$> commandLineOptions) $
      -- Generate Vim file.
      withScope_ (insideScope topLevel) $ generateVimFile $ filePath file

    setScope $ outsideScope topLevel

    reportSLn "scope.top" 50 $ "SCOPE " ++ show (insideScope topLevel)

    syntaxInfo <- stSyntaxInfo <$> get
    i <- buildInterface file topLevel syntaxInfo previousHsImports options

    -- TODO: It would be nice if unsolved things were highlighted
    -- after every mutual block.

    termErrs            <- Fold.toList <$> stTermErrs <$> get
    unsolvedMetas       <- List.nub <$> (mapM getMetaRange =<< getOpenMetas)
    unsolvedConstraints <- getAllConstraints

    ifTopLevelAndHighlightingLevelIs NonInteractive $
      printUnsolvedInfo

    r <- if and [ null termErrs, null unsolvedMetas, null unsolvedConstraints ]
     then do
      -- The file was successfully type-checked (and no warnings were
      -- encountered), so the interface should be written out.
      let ifile = filePath $ toIFile file
      writeInterface ifile i
      return (i, NoWarnings)
     else
      return (i, SomeWarnings $ Warnings termErrs unsolvedMetas unsolvedConstraints)

    -- Print stats
    stats <- Map.toList <$> getStatistics
    case stats of
      []      -> return ()
      _       -> reportS "profile" 1 $ unlines $
        [ "Ticks for " ++ show (pretty mname) ] ++
        [ "  " ++ s ++ " = " ++ show n
        | (s, n) <- sortBy (compare `on` snd) stats ]

    return r

-- | Builds an interface for the current module, which should already
-- have been successfully type checked.

buildInterface :: AbsolutePath
               -> TopLevelInfo
                  -- ^ 'TopLevelInfo' for the current module.
               -> HighlightingInfo
                  -- ^ Syntax highlighting info for the module.
               -> Set String
                  -- ^ Haskell modules imported in imported modules
                  -- (transitively).
               -> [OptionsPragma]
                  -- ^ Options set in @OPTIONS@ pragmas.
               -> TCM Interface
buildInterface file topLevel syntaxInfo previousHsImports pragmas = do
    reportSLn "import.iface" 5 "Building interface..."
    scope'  <- getScope
    let scope = scope' { scopeCurrent = m }
    sig     <- getSignature
    builtin <- gets stLocalBuiltins
    ms      <- getImports
    mhs     <- mapM (\m -> (,) m <$> moduleHash m) $ Set.toList ms
    hsImps  <- getHaskellImports
    patsyns <- getPatternSyns
    h       <- liftIO $ hashFile file
    let	builtin' = Map.mapWithKey (\x b -> fmap (\pf -> (x, primFunName pf)) b) builtin
    reportSLn "import.iface" 7 "  instantiating all meta variables"
    i <- instantiateFull $ Interface
			{ iSourceHash      = h
                        , iImportedModules = mhs
                        , iModuleName      = m
			, iScope	   = publicModules scope
                        , iInsideScope     = insideScope topLevel
			, iSignature	   = sig
			, iBuiltin	   = builtin'
                        , iHaskellImports  = Set.difference hsImps
                                                            previousHsImports
                        , iHighlighting    = syntaxInfo
                        , iPragmaOptions   = pragmas
                        , iPatternSyns     = patsyns
			}
    reportSLn "import.iface" 7 "  interface complete"
    return i
  where m = topLevelModuleName topLevel

-- | Returns (iSourceHash, iFullHash)
getInterfaceFileHashes :: FilePath -> TCM (Maybe (Hash, Hash))
getInterfaceFileHashes ifile = do
  exist <- liftIO $ doesFileExist ifile
  if not exist then return Nothing else do
    (s, close) <- liftIO $ readBinaryFile' ifile
    let hs = decodeHashes s
    liftIO $ maybe 0 (uncurry (+)) hs `seq` close
    return hs

safeReadInterface :: FilePath -> TCM (Maybe Interface)
safeReadInterface ifile = do
  exist <- liftIO $ doesFileExist ifile
  if exist then readInterface ifile
           else return Nothing

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
