{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE RecursiveDo #-}

{-| This module deals with finding imported modules and loading their
    interface files.
-}
module Agda.Interaction.Imports
  ( Mode, pattern ScopeCheck, pattern TypeCheck

  , CheckResult (CheckResult)
  , crModuleInfo
  , crInterface
  , crWarnings
  , crMode
  , crSource

  , Source(..)
  , scopeCheckImport
  , parseSource
  , typeCheckMain

  -- Currently only used by test/api/Issue1168.hs:
  , readInterface
  ) where

import Prelude hiding (null)

import Control.Monad               ( forM, forM_, void )
import Control.Monad.Except
import Control.Monad.IO.Class      ( MonadIO(..) )
import Control.Monad.State
import Control.Monad.Trans.Maybe
import qualified Control.Exception as E

#if __GLASGOW_HASKELL__ < 808
import Control.Monad.Fail (MonadFail)
#endif

import Data.Either
import qualified Data.List as List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text.Lazy as TL

import System.Directory (doesFileExist, removeFile)
import System.FilePath  ( (</>) )

import Agda.Benchmarking

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Attribute
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Parser
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Translation.ConcreteToAbstract as CToA

import Agda.TypeChecking.Errors
import Agda.TypeChecking.Warnings hiding (warnings)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rewriting.Confluence ( checkConfluenceOfRules )
import Agda.TypeChecking.MetaVars ( openMetasToPostulates )
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Serialise
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Pretty as P
import Agda.TypeChecking.DeadCode
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TheTypeChecker

import Agda.Interaction.BasicOps ( getGoals, showGoals )
import Agda.Interaction.FindFile
import Agda.Interaction.Highlighting.Generate
import Agda.Interaction.Highlighting.Precise  ( convert )
import Agda.Interaction.Highlighting.Vim
import Agda.Interaction.Library
import Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens
import Agda.Interaction.Options.Warnings (unsolvedWarnings)
import Agda.Interaction.Response
  (RemoveTokenBasedHighlighting(KeepHighlighting))

import Agda.Utils.FileName
import Agda.Utils.Lens
import Agda.Utils.Maybe
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.IO.Binary
import Agda.Syntax.Common.Pretty hiding (Mode)
import qualified Agda.Utils.ProfileOptions as Profile
import Agda.Utils.Hash
import qualified Agda.Utils.Trie as Trie

import Agda.Utils.Impossible

-- | Whether to ignore interfaces (@.agdai@) other than built-in modules

ignoreInterfaces :: HasOptions m => m Bool
ignoreInterfaces = optIgnoreInterfaces <$> commandLineOptions

-- | Whether to ignore all interface files (@.agdai@)

ignoreAllInterfaces :: HasOptions m => m Bool
ignoreAllInterfaces = optIgnoreAllInterfaces <$> commandLineOptions

-- | The decorated source code.

data Source = Source
  { srcText        :: TL.Text               -- ^ Source code.
  , srcFileType    :: FileType              -- ^ Source file type
  , srcOrigin      :: SourceFile            -- ^ Source location at the time of its parsing
  , srcModule      :: C.Module              -- ^ The parsed module.
  , srcModuleName  :: TopLevelModuleName    -- ^ The top-level module name.
  , srcProjectLibs :: [AgdaLibFile]         -- ^ The .agda-lib file(s) of the project this file belongs to.
  , srcAttributes  :: !Attributes
    -- ^ Every encountered attribute.
  }

-- | Parses a source file and prepares the 'Source' record.

parseSource :: SourceFile -> TCM Source
parseSource sourceFile@(SourceFile f) = Bench.billTo [Bench.Parsing] $ do
  (source, fileType, parsedMod, attrs, parsedModName) <- mdo
    -- This piece of code uses mdo because the top-level module name
    -- (parsedModName) is obtained from the parser's result, but it is
    -- also used by the parser.
    let rf = mkRangeFile f (Just parsedModName)
    source                         <- runPM $ readFilePM rf
    ((parsedMod, attrs), fileType) <- runPM $
                                      parseFile moduleParser rf $
                                      TL.unpack source
    parsedModName                  <- moduleName f parsedMod
    return (source, fileType, parsedMod, attrs, parsedModName)
  libs <- getAgdaLibFiles f parsedModName
  return Source
    { srcText        = source
    , srcFileType    = fileType
    , srcOrigin      = sourceFile
    , srcModule      = parsedMod
    , srcModuleName  = parsedModName
    , srcProjectLibs = libs
    , srcAttributes  = attrs
    }

srcDefaultPragmas :: Source -> [OptionsPragma]
srcDefaultPragmas src = map _libPragmas (srcProjectLibs src)

srcFilePragmas :: Source -> [OptionsPragma]
srcFilePragmas src = pragmas
  where
  cpragmas = C.modPragmas (srcModule src)
  pragmas = [ OptionsPragma
                { pragmaStrings = opts
                , pragmaRange   = r
                }
            | C.OptionsPragma r opts <- cpragmas
            ]

-- | Set options from a 'Source' pragma, using the source
--   ranges of the pragmas for error reporting.
setOptionsFromSourcePragmas :: Source -> TCM ()
setOptionsFromSourcePragmas src = do
  mapM_ setOptionsFromPragma (srcDefaultPragmas src)
  mapM_ setOptionsFromPragma (srcFilePragmas    src)

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

-- | The kind of interface produced by 'createInterface'
moduleCheckMode :: MainInterface -> ModuleCheckMode
moduleCheckMode = \case
    MainInterface TypeCheck                       -> ModuleTypeChecked
    NotMainInterface                              -> ModuleTypeChecked
    MainInterface ScopeCheck                      -> ModuleScopeChecked

-- | Merge an interface into the current proof state.
mergeInterface :: Interface -> TCM ()
mergeInterface i = do
    let sig     = iSignature i
        builtin = Map.toAscList $ iBuiltin i
        primOrBi = \case
          (_, Prim x)                     -> Left x
          (x, Builtin t)                  -> Right (x, Builtin t)
          (x, BuiltinRewriteRelations xs) -> Right (x, BuiltinRewriteRelations xs)
        (prim, bi') = partitionEithers $ map primOrBi builtin
        bi      = Map.fromDistinctAscList bi'
        warns   = iWarnings i
    bs <- getsTC stBuiltinThings
    reportSLn "import.iface.merge" 10 "Merging interface"
    reportSLn "import.iface.merge" 20 $
      "  Current builtins " ++ show (Map.keys bs) ++ "\n" ++
      "  New builtins     " ++ show (Map.keys bi)
    let check (BuiltinName b) (Builtin x) (Builtin y)
              | x == y    = return ()
              | otherwise = typeError $ DuplicateBuiltinBinding b x y
        check _ (BuiltinRewriteRelations xs) (BuiltinRewriteRelations ys) = return ()
        check _ _ _ = __IMPOSSIBLE__
    sequence_ $ Map.intersectionWithKey check bs bi
    addImportedThings
      sig
      (iMetaBindings i)
      bi
      (iPatternSyns i)
      (iDisplayForms i)
      (iUserWarnings i)
      (iPartialDefs i)
      warns
      (iOpaqueBlocks i)
      (iOpaqueNames i)
    reportSLn "import.iface.merge" 20 $
      "  Rebinding primitives " ++ show prim
    mapM_ rebind prim
    whenJustM (optConfluenceCheck <$> pragmaOptions) $ \confChk -> do
      reportSLn "import.iface.confluence" 20 $ "  Checking confluence of imported rewrite rules"
      checkConfluenceOfRules confChk $ concat $ HMap.elems $ sig ^. sigRewriteRules
    where
        rebind (x, q) = do
            PrimImpl _ pf <- lookupPrimitiveFunction x
            stImportedBuiltins `modifyTCLens` Map.insert (someBuiltin x) (Prim pf{ primFunName = q })

addImportedThings
  :: Signature
  -> RemoteMetaStore
  -> BuiltinThings PrimFun
  -> A.PatternSynDefns
  -> DisplayForms
  -> Map A.QName Text      -- ^ Imported user warnings
  -> Set QName             -- ^ Name of imported definitions which are partial
  -> [TCWarning]
  -> Map OpaqueId OpaqueBlock
  -> Map QName OpaqueId
  -> TCM ()
addImportedThings isig metas ibuiltin patsyns display userwarn
                  partialdefs warnings oblock oid = do
  stImports              `modifyTCLens` \ imp -> unionSignatures [imp, isig]
  stImportedMetaStore    `modifyTCLens` HMap.union metas
  stImportedBuiltins     `modifyTCLens` \ imp -> Map.union imp ibuiltin
  stImportedUserWarnings `modifyTCLens` \ imp -> Map.union imp userwarn
  stImportedPartialDefs  `modifyTCLens` \ imp -> Set.union imp partialdefs
  stPatternSynImports    `modifyTCLens` \ imp -> Map.union imp patsyns
  stImportedDisplayForms `modifyTCLens` \ imp -> HMap.unionWith (++) imp display
  stTCWarnings           `modifyTCLens` \ imp -> imp `List.union` warnings
  stOpaqueBlocks         `modifyTCLens` \ imp -> imp `Map.union` oblock
  stOpaqueIds            `modifyTCLens` \ imp -> imp `Map.union` oid
  addImportedInstances isig

-- | Scope checks the given module. A proper version of the module
-- name (with correct definition sites) is returned.

scopeCheckImport ::
  TopLevelModuleName -> ModuleName ->
  TCM (ModuleName, Map ModuleName Scope)
scopeCheckImport top x = do
    reportSLn "import.scope" 5 $ "Scope checking " ++ prettyShow x
    verboseS "import.scope" 10 $ do
      visited <- prettyShow <$> getPrettyVisitedModules
      reportSLn "import.scope" 10 $ "  visited: " ++ visited
    -- Since scopeCheckImport is called from the scope checker,
    -- we need to reimburse her account.
    i <- Bench.billTo [] $ getNonMainInterface top Nothing
    addImport top

    -- If that interface was supposed to raise a warning on import, do so.
    whenJust (iImportWarning i) $ warning . UserWarning

    -- let s = publicModules $ iInsideScope i
    let s = iScope i
    return (iModuleName i `withRangesOfQ` mnameToConcrete x, s)

-- | If the module has already been visited (without warnings), then
-- its interface is returned directly. Otherwise the computation is
-- used to find the interface and the computed interface is stored for
-- potential later use.

alreadyVisited :: TopLevelModuleName ->
                  MainInterface ->
                  PragmaOptions ->
                  TCM ModuleInfo ->
                  TCM ModuleInfo
alreadyVisited x isMain currentOptions getModule =
  case isMain of
    MainInterface TypeCheck                       -> useExistingOrLoadAndRecordVisited ModuleTypeChecked
    NotMainInterface                              -> useExistingOrLoadAndRecordVisited ModuleTypeChecked
    MainInterface ScopeCheck                      -> useExistingOrLoadAndRecordVisited ModuleScopeChecked
  where
  useExistingOrLoadAndRecordVisited :: ModuleCheckMode -> TCM ModuleInfo
  useExistingOrLoadAndRecordVisited mode = fromMaybeM loadAndRecordVisited (existingWithoutWarnings mode)

  -- Case: already visited.
  --
  -- A module with warnings should never be allowed to be
  -- imported from another module.
  existingWithoutWarnings :: ModuleCheckMode -> TCM (Maybe ModuleInfo)
  existingWithoutWarnings mode = runMaybeT $ exceptToMaybeT $ do
    mi <- maybeToExceptT "interface has not been visited in this context" $ MaybeT $
      getVisitedModule x

    when (miMode mi < mode) $
      throwError "previously-visited interface was not sufficiently checked"

    unless (null $ miWarnings mi) $
      throwError "previously-visited interface had warnings"

    reportSLn "import.visit" 10 $ "  Already visited " ++ prettyShow x

    lift $ processResultingModule mi

  processResultingModule :: ModuleInfo -> TCM ModuleInfo
  processResultingModule mi = do
    let ModuleInfo { miInterface = i, miPrimitive = isPrim, miWarnings = ws } = mi

    -- Check that imported options are compatible with current ones (issue #2487),
    -- but give primitive modules a pass
    -- compute updated warnings if needed
    wt <- fromMaybe ws <$> (getOptionsCompatibilityWarnings isMain isPrim currentOptions i)

    return mi { miWarnings = wt }

  loadAndRecordVisited :: TCM ModuleInfo
  loadAndRecordVisited = do
    reportSLn "import.visit" 5 $ "  Getting interface for " ++ prettyShow x
    mi <- processResultingModule =<< getModule
    reportSLn "import.visit" 5 $ "  Now we've looked at " ++ prettyShow x

    -- Interfaces are not stored if we are only scope-checking, or
    -- if any warnings were encountered.
    case (isMain, miWarnings mi) of
      (MainInterface ScopeCheck, _) -> return ()
      (_, _:_)                      -> return ()
      _                             -> storeDecodedModule mi

    reportS "warning.import" 10
      [ "module: " ++ show (moduleNameParts x)
      , "WarningOnImport: " ++ show (iImportWarning (miInterface mi))
      ]

    visitModule mi
    return mi


-- | The result and associated parameters of a type-checked file,
--   when invoked directly via interaction or a backend.
--   Note that the constructor is not exported.

data CheckResult = CheckResult'
  { crModuleInfo :: ModuleInfo
  , crSource'    :: Source
  }

-- | Flattened unidirectional pattern for 'CheckResult' for destructuring inside
--   the 'ModuleInfo' field.
pattern CheckResult :: Interface -> [TCWarning] -> ModuleCheckMode -> Source -> CheckResult
pattern CheckResult { crInterface, crWarnings, crMode, crSource } <- CheckResult'
    { crModuleInfo = ModuleInfo
        { miInterface = crInterface
        , miWarnings = crWarnings
        , miMode = crMode
        }
    , crSource' = crSource
    }

-- | Type checks the main file of the interaction.
--   This could be the file loaded in the interacting editor (emacs),
--   or the file passed on the command line.
--
--   First, the primitive modules are imported.
--   Then, @getInterface@ is called to do the main work.
--
--   If the 'Mode' is 'ScopeCheck', then type-checking is not
--   performed, only scope-checking. (This may include type-checking
--   of imported modules.) In this case the generated, partial
--   interface is not stored in the state ('stDecodedModules'). Note,
--   however, that if the file has already been type-checked, then a
--   complete interface is returned.

typeCheckMain
  :: Mode
     -- ^ Should the file be type-checked, or only scope-checked?
  -> Source
     -- ^ The decorated source code.
  -> TCM CheckResult
typeCheckMain mode src = do
  -- liftIO $ putStrLn $ "This is typeCheckMain " ++ prettyShow f
  -- liftIO . putStrLn . show =<< getVerbosity

  -- For the main interface, we also remember the pragmas from the file
  setOptionsFromSourcePragmas src
  loadPrims <- optLoadPrimitives <$> pragmaOptions

  when loadPrims $ do
    reportSLn "import.main" 10 "Importing the primitive modules."
    libdirPrim <- liftIO getPrimitiveLibDir
    reportSLn "import.main" 20 $ "Library primitive dir = " ++ show libdirPrim
    -- Turn off import-chasing messages.
    -- We have to modify the persistent verbosity setting, since
    -- getInterface resets the current verbosity settings to the persistent ones.

    bracket_ (getsTC Lens.getPersistentVerbosity) Lens.putPersistentVerbosity $ do
      Lens.modifyPersistentVerbosity
        (Strict.Just . Trie.insert [] 0 . Strict.fromMaybe Trie.empty)
        -- set root verbosity to 0

      -- We don't want to generate highlighting information for Agda.Primitive.
      withHighlightingLevel None $
        forM_ (Set.map (libdirPrim </>) Lens.primitiveModules) $ \f -> do
          primSource <- parseSource (SourceFile $ mkAbsolute f)
          checkModuleName' (srcModuleName primSource) (srcOrigin primSource)
          void $ getNonMainInterface (srcModuleName primSource) (Just primSource)

    reportSLn "import.main" 10 $ "Done importing the primitive modules."

  -- Now do the type checking via getInterface.
  checkModuleName' (srcModuleName src) (srcOrigin src)

  mi <- getInterface (srcModuleName src) (MainInterface mode) (Just src)

  stCurrentModule `setTCLens'`
    Just ( iModuleName (miInterface mi)
         , iTopLevelModuleName (miInterface mi)
         )

  return $ CheckResult' mi src
  where
  checkModuleName' m f =
    -- Andreas, 2016-07-11, issue 2092
    -- The error range should be set to the file with the wrong module name
    -- not the importing one (which would be the default).
    setCurrentRange m $ checkModuleName m f Nothing

-- | Tries to return the interface associated to the given (imported) module.
--   The time stamp of the relevant interface file is also returned.
--   Calls itself recursively for the imports of the given module.
--   May type check the module.
--   An error is raised if a warning is encountered.
--
--   Do not use this for the main file, use 'typeCheckMain' instead.

getNonMainInterface
  :: TopLevelModuleName
  -> Maybe Source
     -- ^ Optional: the source code and some information about the source code.
  -> TCM Interface
getNonMainInterface x msrc = do
  -- Preserve/restore the current pragma options, which will be mutated when loading
  -- and checking the interface.
  mi <- bracket_ (useTC stPragmaOptions) (stPragmaOptions `setTCLens`) $
          getInterface x NotMainInterface msrc
  tcWarningsToError $ miWarnings mi
  return (miInterface mi)

-- | A more precise variant of 'getNonMainInterface'. If warnings are
-- encountered then they are returned instead of being turned into
-- errors.

getInterface
  :: TopLevelModuleName
  -> MainInterface
  -> Maybe Source
     -- ^ Optional: the source code and some information about the source code.
  -> TCM ModuleInfo
getInterface x isMain msrc =
  addImportCycleCheck x $ do
     -- We remember but reset the pragma options locally
     -- Issue #3644 (Abel 2020-05-08): Set approximate range for errors in options
     currentOptions <- useTC stPragmaOptions
     setCurrentRange (C.modPragmas . srcModule <$> msrc) $
       -- Now reset the options
       setCommandLineOptions . stPersistentOptions . stPersistentState =<< getTC

     alreadyVisited x isMain currentOptions $ do
      file <- case msrc of
        Nothing  -> findFile x
        Just src -> do
          -- Andreas, 2021-08-17, issue #5508.
          -- So it happened with @msrc == Just{}@ that the file was not added to @ModuleToSource@,
          -- only with @msrc == Nothing@ (then @findFile@ does it).
          -- As a consequence, the file was added later, but with a file name constructed
          -- from a module name.  As #5508 shows, this can be fatal in case-insensitive file systems.
          -- The file name (with case variant) then no longer maps to the module name.
          -- To prevent this, we register the connection in @ModuleToSource@ here,
          -- where we have the correct spelling of the file name.
          let file = srcOrigin src
          modifyTCLens stModuleToSource $ Map.insert x (srcFilePath file)
          pure file
      reportSLn "import.iface" 15 $ List.intercalate "\n" $ map ("  " ++)
        [ "module: " ++ prettyShow x
        , "file:   " ++ prettyShow file
        ]

      reportSLn "import.iface" 10 $ "  Check for cycle"
      checkForImportCycle

      -- -- Andreas, 2014-10-20 AIM XX:
      -- -- Always retype-check the main file to get the iInsideScope
      -- -- which is no longer serialized.
      -- let maySkip = isMain == NotMainInterface
      -- Andreas, 2015-07-13: Serialize iInsideScope again.
      -- Andreas, 2020-05-13 issue #4647: don't skip if reload because of top-level command
      stored <- runExceptT $ Bench.billTo [Bench.Import] $ do
        getStoredInterface x file msrc

      let recheck = \reason -> do
            reportSLn "import.iface" 5 $ concat ["  ", prettyShow x, " is not up-to-date because ", reason, "."]
            setCommandLineOptions . stPersistentOptions . stPersistentState =<< getTC
            case isMain of
              MainInterface _ -> createInterface x file isMain msrc
              NotMainInterface -> createInterfaceIsolated x file msrc

      either recheck pure stored

-- | Check if the options used for checking an imported module are
--   compatible with the current options. Raises Non-fatal errors if
--   not.
checkOptionsCompatible ::
  PragmaOptions -> PragmaOptions -> TopLevelModuleName -> TCM Bool
checkOptionsCompatible current imported importedModule = flip execStateT True $ do
  reportSDoc "import.iface.options" 5 $ P.nest 2 $ "current options  =" P.<+> showOptions current
  reportSDoc "import.iface.options" 5 $ P.nest 2 $ "imported options =" P.<+> showOptions imported
  forM_ infectiveCoinfectiveOptions $ \opt -> do
    unless (icOptionOK opt current imported) $ do
      put False
      warning $
        (case icOptionKind opt of
           Infective   -> InfectiveImport
           Coinfective -> CoInfectiveImport)
        (icOptionWarning opt importedModule)
  where
  showOptions opts =
    P.prettyList $
    map (\opt -> (P.text (icOptionDescription opt) <> ": ") P.<+>
                 P.pretty (icOptionActive opt opts))
      infectiveCoinfectiveOptions

-- | Compare options and return collected warnings.
-- | Returns `Nothing` if warning collection was skipped.

getOptionsCompatibilityWarnings :: MainInterface -> Bool -> PragmaOptions -> Interface -> TCM (Maybe [TCWarning])
getOptionsCompatibilityWarnings isMain isPrim currentOptions i = runMaybeT $ exceptToMaybeT $ do
  -- We're just dropping these reasons-for-skipping messages for now.
  -- They weren't logged before, but they're nice for documenting the early returns.
  when isPrim $
    throwError "Options consistency checking disabled for always-available primitive module"
  whenM (lift $ checkOptionsCompatible currentOptions (iOptionsUsed i)
                  (iTopLevelModuleName i)) $
    throwError "No warnings to collect because options were compatible"
  lift $ getAllWarnings' isMain ErrorWarnings

-- | Try to get the interface from interface file or cache.

getStoredInterface
  :: TopLevelModuleName
     -- ^ Module name of file we process.
  -> SourceFile
     -- ^ File we process.
  -> Maybe Source
  -> ExceptT String TCM ModuleInfo
getStoredInterface x file msrc = do
  -- Check whether interface file exists and is in cache
  --  in the correct version (as testified by the interface file hash).
  --
  -- This is a lazy action which may be skipped if there is no cached interface
  -- and we're ignoring interface files for some reason.
  let getIFileHashesET = do
        -- Check that the interface file exists and return its hash.
        ifile <- maybeToExceptT "the interface file could not be found" $ MaybeT $
          findInterfaceFile' file

        -- Check that the interface file exists and return its hash.
        hashes <- maybeToExceptT "the interface file hash could not be read" $ MaybeT $ liftIO $
          getInterfaceFileHashes ifile

        return (ifile, hashes)

  -- Examine the hash of the interface file. If it is different from the
  -- stored version (in stDecodedModules), or if there is no stored version,
  -- read and decode it. Otherwise use the stored version.
  --
  -- This is a lazy action which may be skipped if the cached or on-disk interface
  -- is invalid, missing, or skipped for some other reason.
  let checkSourceHashET ifaceH = do
        sourceH <- case msrc of
                    Nothing -> liftIO $ hashTextFile (srcFilePath file)
                    Just src -> return $ hashText (srcText src)

        unless (sourceH == ifaceH) $
          throwError $ concat
            [ "the source hash (", show sourceH, ")"
            , " does not match the source hash for the interface (", show ifaceH, ")"
            ]

        reportSLn "import.iface" 5 $ concat ["  ", prettyShow x, " is up-to-date."]

  -- Check if we have cached the module.
  cachedE <- runExceptT $ maybeToExceptT "the interface has not been decoded" $ MaybeT $
      lift $ getDecodedModule x

  case cachedE of
    -- If it's cached ignoreInterfaces has no effect;
    -- to avoid typechecking a file more than once.
    Right mi -> do
      (ifile, hashes) <- getIFileHashesET

      let ifp = filePath $ intFilePath ifile
      let i = miInterface mi

      -- Make sure the hashes match.
      let cachedIfaceHash = iFullHash i
      let fileIfaceHash = snd hashes
      unless (cachedIfaceHash == fileIfaceHash) $ do
        lift $ dropDecodedModule x
        reportSLn "import.iface" 50 $ "  cached hash = " ++ show cachedIfaceHash
        reportSLn "import.iface" 50 $ "  stored hash = " ++ show fileIfaceHash
        reportSLn "import.iface" 5 $ "  file is newer, re-reading " ++ ifp
        throwError $ concat
          [ "the cached interface hash (", show cachedIfaceHash, ")"
          , " does not match interface file (", show fileIfaceHash, ")"
          ]

      Bench.billTo [Bench.Deserialization] $ do
        checkSourceHashET (iSourceHash i)

        reportSLn "import.iface" 5 $ "  using stored version of " ++ (filePath $ intFilePath ifile)
        loadDecodedModule file mi

    Left whyNotCached -> withExceptT (\e -> concat [whyNotCached, " and ", e]) $ do
      whenM ignoreAllInterfaces $
        throwError "we're ignoring all interface files"

      whenM ignoreInterfaces $
        unlessM (lift $ Lens.isBuiltinModule (filePath $ srcFilePath file)) $
            throwError "we're ignoring non-builtin interface files"

      (ifile, hashes) <- getIFileHashesET

      let ifp = (filePath . intFilePath $ ifile)

      Bench.billTo [Bench.Deserialization] $ do
        checkSourceHashET (fst hashes)

        reportSLn "import.iface" 5 $ "  no stored version, reading " ++ ifp

        i <- maybeToExceptT "bad interface, re-type checking" $ MaybeT $
          readInterface ifile

        -- Ensure that the given module name matches the one in the file.
        let topLevelName = iTopLevelModuleName i
        unless (topLevelName == x) $
          -- Andreas, 2014-03-27 This check is now done in the scope checker.
          -- checkModuleName topLevelName file
          lift $ typeError $ OverlappingProjects (srcFilePath file) topLevelName x

        isPrimitiveModule <- lift $ Lens.isPrimitiveModule (filePath $ srcFilePath file)

        lift $ chaseMsg "Loading " x $ Just ifp
        -- print imported warnings
        let ws = filter ((Strict.Just (Just x) ==) .
                         fmap rangeFileName . tcWarningOrigin) $
                 iWarnings i
        unless (null ws) $ alwaysReportSDoc "warning" 1 $ P.vcat $ P.prettyTCM <$> ws

        loadDecodedModule file $ ModuleInfo
          { miInterface = i
          , miWarnings = []
          , miPrimitive = isPrimitiveModule
          , miMode = ModuleTypeChecked
          }


loadDecodedModule
  :: SourceFile
     -- ^ File we process.
  -> ModuleInfo
  -> ExceptT String TCM ModuleInfo
loadDecodedModule file mi = do
  let fp = filePath $ srcFilePath file
  let i = miInterface mi

  -- Check that it's the right version
  reportSLn "import.iface" 5 $ "  imports: " ++ prettyShow (iImportedModules i)

  -- We set the pragma options of the skipped file here, so that
  -- we can check that they are compatible with those of the
  -- imported modules. Also, if the top-level file is skipped we
  -- want the pragmas to apply to interactive commands in the UI.
  -- Jesper, 2021-04-18: Check for changed options in library files!
  -- (see #5250)
  libOptions <- lift $ getLibraryOptions
    (srcFilePath file)
    (iTopLevelModuleName i)
  lift $ mapM_ setOptionsFromPragma (libOptions ++ iFilePragmaOptions i)

  -- Check that options that matter haven't changed compared to
  -- current options (issue #2487)
  unlessM (lift $ Lens.isBuiltinModule fp) $ do
    current <- useTC stPragmaOptions
    when (recheckBecausePragmaOptionsChanged (iOptionsUsed i) current) $
      throwError "options changed"

  -- If any of the imports are newer we need to retype check
  badHashMessages <- fmap lefts $ forM (iImportedModules i) $ \(impName, impHash) -> runExceptT $ do
    reportSLn "import.iface" 30 $ concat ["Checking that module hash of import ", prettyShow impName, " matches ", prettyShow impHash ]
    latestImpHash <- lift $ lift $ setCurrentRange impName $ moduleHash impName
    reportSLn "import.iface" 30 $ concat ["Done checking module hash of import ", prettyShow impName]
    when (impHash /= latestImpHash) $
      throwError $ concat
        [ "module hash for imported module ", prettyShow impName, " is out of date"
        , " (import cached=", prettyShow impHash, ", latest=", prettyShow latestImpHash, ")"
        ]

  unlessNull badHashMessages (throwError . unlines)

  reportSLn "import.iface" 5 "  New module. Let's check it out."
  lift $ mergeInterface i
  Bench.billTo [Bench.Highlighting] $
    lift $ ifTopLevelAndHighlightingLevelIs NonInteractive $
      highlightFromInterface i file

  return mi

-- | Run the type checker on a file and create an interface.
--
--   Mostly, this function calls 'createInterface'.
--   But if it is not the main module we check,
--   we do it in a fresh state, suitably initialize,
--   in order to forget some state changes after successful type checking.

createInterfaceIsolated
  :: TopLevelModuleName
     -- ^ Module name of file we process.
  -> SourceFile
     -- ^ File we process.
  -> Maybe Source
     -- ^ Optional: the source code and some information about the source code.
  -> TCM ModuleInfo
createInterfaceIsolated x file msrc = do
      cleanCachedLog

      ms          <- getImportPath
      range       <- asksTC envRange
      call        <- asksTC envCall
      mf          <- useTC stModuleToSource
      vs          <- getVisitedModules
      ds          <- getDecodedModules
      opts        <- stPersistentOptions . stPersistentState <$> getTC
      isig        <- useTC stImports
      metas       <- useTC stImportedMetaStore
      ibuiltin    <- useTC stImportedBuiltins
      display     <- useTC stImportsDisplayForms
      userwarn    <- useTC stImportedUserWarnings
      partialdefs <- useTC stImportedPartialDefs
      opaqueblk   <- useTC stOpaqueBlocks
      opaqueid    <- useTC stOpaqueIds
      ipatsyns <- getPatternSynImports
      ho       <- getInteractionOutputCallback
      -- Every interface is treated in isolation. Note: Some changes to
      -- the persistent state may not be preserved if an error other
      -- than a type error or an IO exception is encountered in an
      -- imported module.
      (mi, newModToSource, newDecodedModules) <- (either throwError pure =<<) $
           withoutCache $
           -- The cache should not be used for an imported module, and it
           -- should be restored after the module has been type-checked
           freshTCM $
             withImportPath ms $
             localTC (\e -> e
                              -- Andreas, 2014-08-18:
                              -- Preserve the range of import statement
                              -- for reporting termination errors in
                              -- imported modules:
                            { envRange              = range
                            , envCall               = call
                            }) $ do
               setDecodedModules ds
               setCommandLineOptions opts
               setInteractionOutputCallback ho
               stModuleToSource `setTCLens` mf
               setVisitedModules vs
               addImportedThings isig metas ibuiltin ipatsyns display
                 userwarn partialdefs [] opaqueblk opaqueid

               r  <- createInterface x file NotMainInterface msrc
               mf' <- useTC stModuleToSource
               ds' <- getDecodedModules
               return (r, mf', ds')

      stModuleToSource `setTCLens` newModToSource
      setDecodedModules newDecodedModules

      -- We skip the file which has just been type-checked to
      -- be able to forget some of the local state from
      -- checking the module.
      -- Note that this doesn't actually read the interface
      -- file, only the cached interface. (This comment is not
      -- correct, see
      -- test/Fail/customised/NestedProjectRoots.err.)
      validated <- runExceptT $ loadDecodedModule file mi

      -- NOTE: This attempts to type-check FOREVER if for some
      -- reason it continually fails to validate interface.
      let recheckOnError = \msg -> do
            alwaysReportSLn "import.iface" 1 $ "Failed to validate just-loaded interface: " ++ msg
            createInterfaceIsolated x file msrc

      either recheckOnError pure validated


-- | Formats and outputs the "Checking", "Finished" and "Loading " messages.

chaseMsg
  :: String               -- ^ The prefix, like @Checking@, @Finished@, @Loading @.
  -> TopLevelModuleName   -- ^ The module name.
  -> Maybe String         -- ^ Optionally: the file name.
  -> TCM ()
chaseMsg kind x file = do
  indentation <- (`replicate` ' ') <$> asksTC (pred . length . envImportPath)
  traceImports <- optTraceImports <$> commandLineOptions
  let maybeFile = caseMaybe file "." $ \ f -> " (" ++ f ++ ")."
      vLvl | kind == "Checking"
             && traceImports > 0 = 1
           | kind == "Finished"
             && traceImports > 1 = 1
           | List.isPrefixOf "Loading" kind
             && traceImports > 2 = 1
           | otherwise = 2
  alwaysReportSLn "import.chase" vLvl $ concat
    [ indentation, kind, " ", prettyShow x, maybeFile ]

-- | Print the highlighting information contained in the given interface.

highlightFromInterface
  :: Interface
  -> SourceFile
     -- ^ The corresponding file.
  -> TCM ()
highlightFromInterface i file = do
  reportSLn "import.iface" 5 $
    "Generating syntax info for " ++ filePath (srcFilePath file) ++
    " (read from interface)."
  printHighlightingInfo KeepHighlighting (iHighlighting i)

-- | Read interface file corresponding to a module.

readInterface :: InterfaceFile -> TCM (Maybe Interface)
readInterface file = do
    let ifp = filePath $ intFilePath file
    -- Decode the interface file
    (s, close) <- liftIO $ readBinaryFile' ifp
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
    handler = \case
      IOException _ _ e -> do
        alwaysReportSLn "" 0 $ "IO exception: " ++ show e
        return Nothing   -- Work-around for file locking bug.
                         -- TODO: What does this refer to? Please
                         -- document.
      e -> throwError e

-- | Writes the given interface to the given file.
--
-- The written interface is decoded and returned.

writeInterface :: AbsolutePath -> Interface -> TCM Interface
writeInterface file i = let fp = filePath file in do
    reportSLn "import.iface.write" 5  $
      "Writing interface file " ++ fp ++ "."
    -- Andreas, 2015-07-13
    -- After QName memoization (AIM XXI), scope serialization might be cheap enough.
    -- -- Andreas, Makoto, 2014-10-18 AIM XX:
    -- -- iInsideScope is bloating the interface files, so we do not serialize it?
    -- i <- return $
    --   i { iInsideScope  = emptyScopeInfo
    --     }
    -- [Old: Andreas, 2016-02-02 this causes issue #1804, so don't do it:]
    -- Andreas, 2020-05-13, #1804, #4647: removed private declarations
    -- only when we actually write the interface.
    let filteredIface = i { iInsideScope  = withoutPrivates $ iInsideScope i }
    reportSLn "import.iface.write" 50 $
      "Writing interface file with hash " ++ show (iFullHash filteredIface) ++ "."
    encodedIface <- encodeFile fp filteredIface
    reportSLn "import.iface.write" 5 "Wrote interface file."
    fromMaybe __IMPOSSIBLE__ <$> (Bench.billTo [Bench.Deserialization] (decode encodedIface))
  `catchError` \e -> do
    alwaysReportSLn "" 1 $
      "Failed to write interface " ++ fp ++ "."
    liftIO $
      whenM (doesFileExist fp) $ removeFile fp
    throwError e

-- | Tries to type check a module and write out its interface. The
-- function only writes out an interface file if it does not encounter
-- any warnings.
--
-- If appropriate this function writes out syntax highlighting
-- information.

createInterface
  :: TopLevelModuleName    -- ^ The expected module name.
  -> SourceFile            -- ^ The file to type check.
  -> MainInterface         -- ^ Are we dealing with the main module?
  -> Maybe Source      -- ^ Optional information about the source code.
  -> TCM ModuleInfo
createInterface mname file isMain msrc = do
  let x = mname
  let fp = filePath $ srcFilePath file
  let checkMsg = case isMain of
                   MainInterface ScopeCheck -> "Reading "
                   _                        -> "Checking"
      withMsgs = bracket_
       (chaseMsg checkMsg x $ Just fp)
       (const $ do ws <- getAllWarnings AllWarnings
                   let classified = classifyWarnings ws
                   let wa' = filter ((Strict.Just (Just mname) ==) .
                                     fmap rangeFileName . tcWarningOrigin) $
                             tcWarnings classified
                   unless (null wa') $
                     alwaysReportSDoc "warning" 1 $ P.vcat $ P.prettyTCM <$> wa'
                   when (null (nonFatalErrors classified)) $ chaseMsg "Finished" x Nothing)

  withMsgs $
    Bench.billTo [Bench.TopModule mname] $
    localTC (\e -> e { envCurrentPath = Just (srcFilePath file) }) $ do

    let onlyScope = isMain == MainInterface ScopeCheck

    reportSLn "import.iface.create" 5 $
      "Creating interface for " ++ prettyShow mname ++ "."
    verboseS "import.iface.create" 10 $ do
      visited <- prettyShow <$> getPrettyVisitedModules
      reportSLn "import.iface.create" 10 $ "  visited: " ++ visited

    src <- maybe (parseSource file) pure msrc

    let srcPath = srcFilePath $ srcOrigin src

    fileTokenInfo <- Bench.billTo [Bench.Highlighting] $
      generateTokenInfoFromSource
        (let !top = srcModuleName src in
         mkRangeFile srcPath (Just top))
        (TL.unpack $ srcText src)
    stTokens `modifyTCLens` (fileTokenInfo <>)

    setOptionsFromSourcePragmas src
    checkAttributes (srcAttributes src)
    syntactic <- optSyntacticEquality <$> pragmaOptions
    localTC (\env -> env { envSyntacticEqualityFuel = syntactic }) $ do

    verboseS "import.iface.create" 15 $ do
      nestingLevel      <- asksTC (pred . length . envImportPath)
      highlightingLevel <- asksTC envHighlightingLevel
      reportSLn "import.iface.create" 15 $ unlines
        [ "  nesting      level: " ++ show nestingLevel
        , "  highlighting level: " ++ show highlightingLevel
        ]

    -- Scope checking.
    reportSLn "import.iface.create" 7 "Starting scope checking."
    topLevel <- Bench.billTo [Bench.Scoping] $ do
      let topDecls = C.modDecls $ srcModule src
      concreteToAbstract_ (TopLevel srcPath mname topDecls)
    reportSLn "import.iface.create" 7 "Finished scope checking."

    let ds    = topLevelDecls topLevel
        scope = topLevelScope topLevel

    -- Highlighting from scope checker.
    reportSLn "import.iface.create" 7 "Starting highlighting from scope."
    Bench.billTo [Bench.Highlighting] $ do
      -- Generate and print approximate syntax highlighting info.
      ifTopLevelAndHighlightingLevelIs NonInteractive $
        printHighlightingInfo KeepHighlighting fileTokenInfo
      ifTopLevelAndHighlightingLevelIsOr NonInteractive onlyScope $
        mapM_ (\ d -> generateAndPrintSyntaxInfo d Partial onlyScope) ds
    reportSLn "import.iface.create" 7 "Finished highlighting from scope."


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

    if onlyScope
      then do
        reportSLn "import.iface.create" 7 "Skipping type checking."
        cacheCurrentLog
      else do
        reportSLn "import.iface.create" 7 "Starting type checking."
        Bench.billTo [Bench.Typing] $ mapM_ checkDeclCached ds `finally_` cacheCurrentLog
        reportSLn "import.iface.create" 7 "Finished type checking."

    -- Ulf, 2013-11-09: Since we're rethrowing the error, leave it up to the
    -- code that handles that error to reset the state.
    -- Ulf, 2013-11-13: Errors are now caught and highlighted in InteractionTop.
    -- catchError_ (checkDecls ds) $ \e -> do
    --   ifTopLevelAndHighlightingLevelIs NonInteractive $
    --     printErrorInfo e
    --   throwError e

    unfreezeMetas

    -- Profiling: Count number of metas.
    whenProfile Profile.Metas $ do
      m <- fresh
      tickN "metas" (fromIntegral (metaId m))

    -- Highlighting from type checker.
    reportSLn "import.iface.create" 7 "Starting highlighting from type info."
    Bench.billTo [Bench.Highlighting] $ do

      -- Move any remaining token highlighting to stSyntaxInfo.
      toks <- useTC stTokens
      ifTopLevelAndHighlightingLevelIs NonInteractive $
        printHighlightingInfo KeepHighlighting toks
      stTokens `setTCLens` mempty

      -- Grabbing warnings and unsolved metas to highlight them
      warnings <- getAllWarnings AllWarnings
      unless (null warnings) $ reportSDoc "import.iface.create" 20 $
        "collected warnings: " <> prettyTCM warnings
      unsolved <- getAllUnsolvedWarnings
      unless (null unsolved) $ reportSDoc "import.iface.create" 20 $
        "collected unsolved: " <> prettyTCM unsolved
      let warningInfo =
            convert $ foldMap warningHighlighting $ unsolved ++ warnings

      stSyntaxInfo `modifyTCLens` \inf -> (inf `mappend` toks) `mappend` warningInfo

      whenM (optGenerateVimFile <$> commandLineOptions) $
        -- Generate Vim file.
        withScope_ scope $ generateVimFile $ filePath $ srcPath
    reportSLn "import.iface.create" 7 "Finished highlighting from type info."

    setScope scope
    reportSLn "scope.top" 50 $ "SCOPE " ++ show scope

    -- TODO: It would be nice if unsolved things were highlighted
    -- after every mutual block.

    openMetas           <- getOpenMetas
    unless (null openMetas) $ do
      reportSLn "import.metas" 10 "We have unsolved metas."
      reportSLn "import.metas" 10 =<< showGoals =<< getGoals

    ifTopLevelAndHighlightingLevelIs NonInteractive printUnsolvedInfo

    -- Andreas, 2016-08-03, issue #964
    -- When open metas are allowed,
    -- permanently freeze them now by turning them into postulates.
    -- This will enable serialization.
    -- savedMetaStore <- useTC stMetaStore
    unless (includeStateChanges isMain) $
      -- Andreas, 2018-11-15, re issue #3393:
      -- We do not get here when checking the main module
      -- (then includeStateChanges is True).
      whenM (optAllowUnsolved <$> pragmaOptions) $ do
        reportSLn "import.iface.create" 7 "Turning unsolved metas (if any) into postulates."
        withCurrentModule (scope ^. scopeCurrent) openMetasToPostulates
        -- Clear constraints as they might refer to what
        -- they think are open metas.
        stAwakeConstraints    `setTCLens` []
        stSleepingConstraints `setTCLens` []

    -- Serialization.
    reportSLn "import.iface.create" 7 "Starting serialization."
    i <- Bench.billTo [Bench.Serialization, Bench.BuildInterface] $
      buildInterface src topLevel

    reportS "tc.top" 101 $
      "Signature:" :
      [ unlines
          [ prettyShow q
          , "  type: " ++ show (defType def)
          , "  def:  " ++ show cc
          ]
      | (q, def) <- HMap.toList $ iSignature i ^. sigDefinitions,
        Function{ funCompiled = cc } <- [theDef def]
      ]
    reportSLn "import.iface.create" 7 "Finished serialization."

    mallWarnings <- getAllWarnings' isMain ErrorWarnings

    reportSLn "import.iface.create" 7 "Considering writing to interface file."
    finalIface <- constructIScope <$> case (mallWarnings, isMain) of
      (_:_, _) -> do
        -- Andreas, 2018-11-15, re issue #3393
        -- The following is not sufficient to fix #3393
        -- since the replacement of metas by postulates did not happen.
        -- -- | not (allowUnsolved && all (isUnsolvedWarning . tcWarning) allWarnings) -> do
        reportSLn "import.iface.create" 7 "We have warnings, skipping writing interface file."
        return i
      ([], MainInterface ScopeCheck) -> do
        reportSLn "import.iface.create" 7 "We are just scope-checking, skipping writing interface file."
        return i
      ([], _) -> Bench.billTo [Bench.Serialization] $ do
        reportSLn "import.iface.create" 7 "Actually calling writeInterface."
        -- The file was successfully type-checked (and no warnings were
        -- encountered), so the interface should be written out.
        ifile <- toIFile file
        serializedIface <- writeInterface ifile i
        reportSLn "import.iface.create" 7 "Finished writing to interface file."
        return serializedIface

    -- -- Restore the open metas, as we might continue in interaction mode.
    -- Actually, we do not serialize the metas if checking the MainInterface
    -- stMetaStore `setTCLens` savedMetaStore

    -- Profiling: Print statistics.
    printStatistics (Just mname) =<< getStatistics

    -- Get the statistics of the current module
    -- and add it to the accumulated statistics.
    localStatistics <- getStatistics
    lensAccumStatistics `modifyTCLens` Map.unionWith (+) localStatistics
    reportSLn "import.iface" 5 "Accumulated statistics."

    isPrimitiveModule <- Lens.isPrimitiveModule (filePath srcPath)

    return ModuleInfo
      { miInterface = finalIface
      , miWarnings = mallWarnings
      , miPrimitive = isPrimitiveModule
      , miMode = moduleCheckMode isMain
      }

-- | Expert version of 'getAllWarnings'; if 'isMain' is a
-- 'MainInterface', the warnings definitely include also unsolved
-- warnings.

getAllWarnings' :: (MonadFail m, ReadTCState m, MonadWarning m, MonadTCM m) => MainInterface -> WhichWarnings -> m [TCWarning]
getAllWarnings' (MainInterface _) = getAllWarningsPreserving unsolvedWarnings
getAllWarnings' NotMainInterface  = getAllWarningsPreserving Set.empty

-- Andreas, issue 964: not checking null interactionPoints
-- anymore; we want to serialize with open interaction points now!

-- | Reconstruct the 'iScope' (not serialized)
--   from the 'iInsideScope' (serialized).

constructIScope :: Interface -> Interface
constructIScope i = billToPure [ Deserialization ] $
  i{ iScope = publicModules $ iInsideScope i }

-- | Builds an interface for the current module, which should already
-- have been successfully type checked.

buildInterface
  :: Source
     -- ^ 'Source' for the current module.
  -> TopLevelInfo
     -- ^ 'TopLevelInfo' scope information for the current module.
  -> TCM Interface
buildInterface src topLevel = do
    reportSLn "import.iface" 5 "Building interface..."
    let mname = CToA.topLevelModuleName topLevel
        source   = srcText src
        fileType = srcFileType src
        defPragmas = srcDefaultPragmas src
        filePragmas  = srcFilePragmas src
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
    builtin     <- useTC stLocalBuiltins
    mhs         <- mapM (\top -> (top,) <$> moduleHash top) .
                   Set.toAscList =<<
                   useR stImportedModules
    foreignCode <- useTC stForeignCode
    -- Ulf, 2016-04-12:
    -- Non-closed display forms are not applicable outside the module anyway,
    -- and should be dead-code eliminated (#1928).
    origDisplayForms <- HMap.filter (not . null) . HMap.map (filter isClosed) <$> useTC stImportsDisplayForms
    -- TODO: Kill some ranges?
    let scope = topLevelScope topLevel
    -- Andreas, Oskar, 2023-10-19, issue #6931:
    -- To not delete module telescopes of empty public modules,
    -- we need to pass the public modules to the dead-code elimination
    -- (to be mined for additional roots for the reachability analysis).
    (display, sig, solvedMetas) <-
      eliminateDeadCode (publicModules scope) builtin origDisplayForms ==<<
        (getSignature, useR stSolvedMetaStore)
    userwarns   <- useTC stLocalUserWarnings
    importwarn  <- useTC stWarningOnImport
    syntaxInfo  <- useTC stSyntaxInfo
    optionsUsed <- useTC stPragmaOptions
    partialDefs <- useTC stLocalPartialDefs

    -- Only serialise the opaque blocks actually defined in this
    -- top-level module.
    opaqueBlocks' <- useTC stOpaqueBlocks
    opaqueIds' <- useTC stOpaqueIds
    let
      mh = moduleNameId (srcModuleName src)
      opaqueBlocks = Map.filterWithKey (\(OpaqueId _ mod) _ -> mod == mh) opaqueBlocks'
      isLocal qnm = case nameId (qnameName qnm) of
        NameId _ mh' -> mh' == mh
      opaqueIds = Map.filterWithKey (\qnm (OpaqueId _ mod) -> isLocal qnm || mod == mh) opaqueIds'

    -- Andreas, 2015-02-09 kill ranges in pattern synonyms before
    -- serialization to avoid error locations pointing to external files
    -- when expanding a pattern synonym.
    patsyns <- killRange <$> getPatternSyns
    let builtin' = Map.mapWithKey (\ x b -> primName x <$> b) builtin
    warnings <- getAllWarnings AllWarnings
    let i = Interface
          { iSourceHash      = hashText source
          , iSource          = source
          , iFileType        = fileType
          , iImportedModules = mhs
          , iModuleName      = mname
          , iTopLevelModuleName = srcModuleName src
          , iScope           = empty -- publicModules scope
          , iInsideScope     = scope
          , iSignature       = sig
          , iMetaBindings    = solvedMetas
          , iDisplayForms    = display
          , iUserWarnings    = userwarns
          , iImportWarning   = importwarn
          , iBuiltin         = builtin'
          , iForeignCode     = foreignCode
          , iHighlighting    = syntaxInfo
          , iDefaultPragmaOptions = defPragmas
          , iFilePragmaOptions    = filePragmas
          , iOptionsUsed     = optionsUsed
          , iPatternSyns     = patsyns
          , iWarnings        = warnings
          , iPartialDefs     = partialDefs
          , iOpaqueBlocks    = opaqueBlocks
          , iOpaqueNames     = opaqueIds
          }
    i <-
      ifM (optSaveMetas <$> pragmaOptions)
        (return i)
        (do reportSLn "import.iface" 7
              "  instantiating all meta variables"
            -- Note that the meta-variables in the definitions in
            -- "sig" have already been instantiated (by
            -- eliminateDeadCode).
            instantiateFullExceptForDefinitions i)
    reportSLn "import.iface" 7 "  interface complete"
    return i

    where
      primName (PrimitiveName x) b = (x, primFunName b)
      primName (BuiltinName x)   b = __IMPOSSIBLE__

-- | Returns (iSourceHash, iFullHash)
--   We do not need to check that the file exist because we only
--   accept @InterfaceFile@ as an input and not arbitrary @AbsolutePath@!
getInterfaceFileHashes :: InterfaceFile -> IO (Maybe (Hash, Hash))
getInterfaceFileHashes fp = do
  let ifile = filePath $ intFilePath fp
  (s, close) <- readBinaryFile' ifile
  let hs = decodeHashes s
  maybe 0 (uncurry (+)) hs `seq` close
  return hs

moduleHash :: TopLevelModuleName -> TCM Hash
moduleHash m = iFullHash <$> getNonMainInterface m Nothing
