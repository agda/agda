{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}

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
  , scopeCheckFileImport
  , parseSource
  , typeCheckMain
  , getNonMainInterface
  , getNonMainModuleInfo
  , getInterface
  , importPrimitiveModules
  , raiseNonFatalErrors

  -- Currently only used by test/api/Issue1168.hs:
  , readInterface
  ) where

import Prelude hiding (null)

import Control.Monad.Except        ( MonadError(..), ExceptT, runExceptT, withExceptT )
import Control.Monad.IO.Class      ( MonadIO(..) )
import Control.Monad.State         ( MonadState(..), execStateT )
import Control.Monad.Trans.Maybe
import qualified Control.Exception as E

import Data.Either
import Data.List (intercalate)
import qualified Data.List as List
import Data.Maybe
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HMap
import qualified Data.ByteString as B
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL

import System.Directory (doesFileExist, removeFile)
import System.FilePath  ( (</>) )
import System.IO

import Agda.Benchmarking

import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Concrete.Attribute
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Common
import Agda.Syntax.Common.Pretty hiding (Mode)
import Agda.Syntax.Parser
import Agda.Syntax.Position
import Agda.Syntax.Scope.Base
import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Translation.ConcreteToAbstract
  ( TopLevel( TopLevel )
  , TopLevelInfo( TopLevelInfo, topLevelDecls, topLevelScope)
  , checkAttributes, concreteToAbstract_
  )
import qualified Agda.Syntax.Translation.ConcreteToAbstract as CToA

import Agda.TypeChecking.InstanceArguments
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Warnings hiding (warnings)
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Rewriting.Confluence ( checkConfluenceOfRules, sortRulesOfSymbol )
import Agda.TypeChecking.MetaVars ( openMetasToPostulates )
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Serialise (decode, encodeFile, decodeInterface, deserializeHashes)
import Agda.TypeChecking.Primitive
import Agda.TypeChecking.Pretty as P
import Agda.TypeChecking.DeadCode
import qualified Agda.TypeChecking.Monad.Benchmark as Bench

import Agda.TheTypeChecker

import Agda.Interaction.BasicOps ( getGoals, prettyGoals )
import Agda.Interaction.FindFile
import Agda.Interaction.Highlighting.Generate
import qualified Agda.Interaction.Highlighting.Precise as Highlighting ( convert )
import Agda.Interaction.Highlighting.Vim
import Agda.Interaction.Library
import Agda.Interaction.Options
import qualified Agda.Interaction.Options.Lenses as Lens
import Agda.Interaction.Options.Warnings (unsolvedWarnings)
import Agda.Interaction.Response
  (RemoveTokenBasedHighlighting(KeepHighlighting))

import Agda.Utils.CallStack (HasCallStack)
import Agda.Utils.FileName
import Agda.Utils.Hash
import Agda.Utils.IO.Binary
import Agda.Utils.Lens
import Agda.Utils.List ( nubOn )
import Agda.Utils.Maybe
import qualified Agda.Utils.Maybe.Strict as Strict
import Agda.Utils.Monad
import Agda.Utils.Null
import qualified Agda.Interaction.Options.ProfileOptions as Profile
import Agda.Utils.Singleton
import qualified Agda.Utils.Set1 as Set1
import qualified Agda.Utils.Trie as Trie

import Agda.Utils.Impossible
import System.IO.Error (isUserError, isFullError)
import Agda.TypeChecking.Rewriting.NonLinPattern (getMatchables)

-- | Whether to ignore interfaces (@.agdai@) other than built-in modules

ignoreInterfaces :: HasOptions m => m Bool
ignoreInterfaces = optIgnoreInterfaces <$> commandLineOptions

-- | Whether to ignore all interface files (@.agdai@)

ignoreAllInterfaces :: HasOptions m => m Bool
ignoreAllInterfaces = optIgnoreAllInterfaces <$> commandLineOptions

-- | Whether to write interface files (@.agdai@)

writeInterfaces :: HasOptions m => m Bool
writeInterfaces = optWriteInterfaces <$> commandLineOptions

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
parseSource sourceFile = Bench.billTo [Bench.Parsing] $ do
  -- Issue #7303:
  -- The parser previously used mdo to avoid the duplicate parsing for the
  -- bootstrapping of the TopLevelModuleName in Range.
  -- But that made ranges blackholes during parsing,
  -- introducing regression #7301, fragility of the API as observed in #7492,
  -- and debugging headaches as ranges could not be showed during parsing.
  -- Now we bite the bullet to parse the source twice,
  -- until a better management of ranges comes about.
  --
  -- (E.g. it is unclear why ranges need the file name/id in place
  -- so early, as all the ranges from one file have the same file id.
  -- It would be sufficient to fill in the file name/id when the mixing
  -- with other files starts, e.g. during scope checking.)

  f <- srcFilePath sourceFile

  -- Read the source text.
  let rf0 = mkRangeFile f Nothing
  setCurrentRange (beginningOfFile rf0) do

  source <- runPM $ readFilePM rf0
  let txt = TL.unpack source

  -- Bootstrapping: parse the module name.
  parsedModName0 <- moduleName f . fst . fst =<< do
    runPMDropWarnings $ parseFile moduleParser rf0 txt

  -- Now parse again, with module name present to be filled into the ranges.
  let rf = mkRangeFile f $ Just parsedModName0
  ((parsedMod, attrs), fileType) <- runPM $ parseFile moduleParser rf txt
  parsedModName                  <- moduleName f parsedMod

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


-- | Computes the module name of the top-level module in the given file.
--
-- If no top-level module name is given, then an attempt is made to
-- use the file name as a module name.

moduleName ::
     AbsolutePath
     -- ^ The path to the file.
  -> C.Module
     -- ^ The parsed module.
  -> TCM TopLevelModuleName
moduleName file parsedModule = Bench.billTo [Bench.ModuleName] $ do
  let defaultName = rootNameModule file
      raw         = rawTopLevelModuleNameForModule parsedModule
  topLevelModuleName =<< if isNoName raw
    then setCurrentRange (rangeFromAbsolutePath file) do
      m <- runPM (fst <$> parse moduleNameParser defaultName)
             `catchError` \_ ->
           typeError $ InvalidFileName file DoesNotCorrespondToValidModuleName
      case m of
        C.Qual{} ->
          typeError $ InvalidFileName file $
            RootNameModuleNotAQualifiedModuleName $ T.pack defaultName
        C.QName{} ->
          return $ RawTopLevelModuleName
            { rawModuleNameRange = getRange m
            , rawModuleNameParts = singleton (T.pack defaultName)
            , rawModuleNameInferred = True
                -- Andreas, 2025-06-21, issue #7953:
                -- Remember we made up this module name to improve errors.
            }
    else return raw


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
--   ranges of the pragmas for error reporting. Flag to check consistency.
setOptionsFromSourcePragmas :: Bool -> Source -> TCM ()
setOptionsFromSourcePragmas checkOpts src = do
  mapM_ setOpts (srcDefaultPragmas src)
  mapM_ setOpts (srcFilePragmas    src)
  where
    setOpts | checkOpts = checkAndSetOptionsFromPragma
            | otherwise = setOptionsFromPragma

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
    reportSLn "import.iface.merge" 10 $ "Merging interface " ++ prettyShow (iTopLevelModuleName i)
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

    reportSLn "import.iface.merge" 50 $
      "  Rebinding primitives " ++ show prim
    mapM_ rebind prim
    whenJustM (optConfluenceCheck <$> pragmaOptions) \ confChk -> do
      let rews = concat $ HMap.elems $ sig ^. sigRewriteRules
      verboseS "import.iface.confluence" 20 do
        if null rews then reportSLn "" 1 $ "  No rewrite rules imported"
        else do
          reportSDoc "" 1 $ P.vcat $ map (P.nest 2) $
            "Checking confluence of imported rewrite rules" :
            map (("-" P.<+>) . prettyTCM . rewName) rews

      -- Andreas, 2025-06-28, PR #7934 and issue #7969:
      -- Global confluence checker requires rules to be sorted
      -- according to the generality of their lhs
      when (confChk == GlobalConfluenceCheck) $
        forM_ (nubOn id $ map rewHead rews) sortRulesOfSymbol
      checkConfluenceOfRules confChk rews
    where
        rebind (x, q) = do
            PrimImpl _ pf <- lookupPrimitiveFunction x
            stImportedBuiltins `modifyTCLens` Map.insert (someBuiltin x) (Prim pf{ primFunName = q })

addImportedThings
  :: Signature
  -> RemoteMetaStore
  -> BuiltinThings
  -> A.PatternSynDefns
  -> DisplayForms
  -> UserWarnings      -- ^ Imported user warnings
  -> Set QName             -- ^ Name of imported definitions which are partial
  -> Set TCWarning
  -> Map OpaqueId OpaqueBlock
  -> Map QName OpaqueId
  -> TCM ()
addImportedThings isig metas ibuiltin patsyns display userwarn
                  partialdefs warnings oblock oid = do
  stImports              `modifyTCLens` \ imp -> importSignature imp isig
  stImportedMetaStore    `modifyTCLens` HMap.union metas
  stImportedBuiltins     `modifyTCLens` \ imp -> Map.union imp ibuiltin
  stImportedUserWarnings `modifyTCLens` \ imp -> Map.union imp userwarn
  stImportedPartialDefs  `modifyTCLens` \ imp -> Set.union imp partialdefs
  stPatternSynImports    `modifyTCLens` \ imp -> Map.union imp patsyns
  stImportedDisplayForms `modifyTCLens` \ imp -> HMap.unionWith (<>) imp display
  stTCWarnings           `modifyTCLens` \ imp -> Set.union imp warnings
  stOpaqueBlocks         `modifyTCLens` \ imp -> imp `Map.union` oblock
  stOpaqueIds            `modifyTCLens` \ imp -> imp `Map.union` oid

-- | Merges two signatures, assuming the second is being imported into the first
--
-- This is not commutative: `Map.union` is left-biased and we also assume that
-- updates from rewrite rules in the first signature do not need to be
-- re-applied (rewrite rules in the current signature cannot refer to
-- definitions that are not in the current signature)
importSignature ::
     Signature
       -- ^ Current signature
  -> Signature
       -- ^ Signature being imported
  -> Signature
       -- ^ Merged signature
importSignature (Sig a b c d) (Sig a' b' c' d') =
  Sig (Map.union a a')
      (fixupDefs $ HMap.union b b') -- definitions are unique (in at most one module) but need to be fixed to account for the new rewrite rules
      (HMap.unionWith mappend c c') -- rewrite rules are accumulated
      (d <> d')                     -- instances are accumulated
  where
    -- #8218: Rewrite rules can modify the signature (e.g. definitional
    -- injectivity of the head symbol). We need to replay these adjustments when
    -- importing because rewrite rules might be defined in a different module
    -- from the definitions they modify.
    fixupDefs ds = foldr (\(f, rews) -> updateDefsForRewrites f rews
                                      $ rews >>= getMatchables)
                         ds (HMap.toList c')

-- | Scope checks the given module, generating an interface or retrieving an existing one.
--   Returns the module name and exported scope from the interface.
--
scopeCheckFileImport ::
     TopLevelModuleName
  -> TCM (ModuleName, Map ModuleName Scope)
scopeCheckFileImport top = do
    reportSLn "import.scope" 15 $ "Scope checking " ++ prettyShow top
    verboseS "import.scope" 30 $ do
      visited <- prettyShow <$> getPrettyVisitedModules
      reportSLn "import.scope" 30 $ "  visited: " ++ visited
    -- Since scopeCheckImport is called from the scope checker,
    -- we need to reimburse her account.
    i <- Bench.billTo [] $ getNonMainInterface top Nothing
    addImport top

    -- Print list of imported modules in current state.
    verboseS "import.iface.imports" 10 do
      imports <- Set.toList <$> useTC stImportedModules
      reportSLn "import.iface.imports" 10 $ intercalate "\n" $
        unwords [prettyShow top, "added, all imports:"] :
        map (\ x -> unwords [ " ", "-", prettyShow x ]) imports

    -- Print list of transitively imported modules in current state.
    verboseS "import.iface.imports" 20 do
      imports <- Set.toList <$> useTC stImportedModulesTransitive
      reportSLn "import.iface.imports" 10 $ intercalate "\n" $
        unwords [prettyShow top, "added, all transitive imports:"] :
        map (\ x -> unwords [ " ", "-", prettyShow x ]) imports

    -- If that interface was supposed to raise a warning on import, do so.
    whenJust (iImportWarning i) $ warning . UserWarning

    -- let s = publicModules $ iInsideScope i
    let s = iScope i
    return (iModuleName i, s)

-- | The result and associated parameters of a type-checked file,
--   when invoked directly via interaction or a backend.
--   Note that the constructor is not exported.

data CheckResult = CheckResult'
  { crModuleInfo :: ModuleInfo
  , crSource'    :: Source
  }

-- | Flattened unidirectional pattern for 'CheckResult' for destructuring inside
--   the 'ModuleInfo' field.
pattern CheckResult :: Interface -> Set TCWarning -> ModuleCheckMode -> Source -> CheckResult
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
  setOptionsFromSourcePragmas True src

  -- Import the Agda.Primitive modules
  importPrimitiveModules

  -- Now do the type checking via getInterface.
  checkModuleName' (srcModuleName src) (srcOrigin src)

  mi <- getInterface (srcModuleName src) (MainInterface mode) (Just src)

  stCurrentModule `setTCLens'`
    Just ( iModuleName (miInterface mi)
         , iTopLevelModuleName (miInterface mi)
         )

  return $ CheckResult' mi src

-- Andreas, 2016-07-11, issue 2092
-- The error range should be set to the file with the wrong module name
-- not the importing one (which would be the default).
checkModuleName' :: TopLevelModuleName' Range -> SourceFile -> TCM ()
checkModuleName' m f =
  setCurrentRange m $ checkModuleName m f Nothing

-- | Import the primitive modules (unless --no-load-primitives).
importPrimitiveModules :: TCM ()
importPrimitiveModules = whenM (optLoadPrimitives <$> pragmaOptions) $ do
  reportSLn "import.main" 10 "Importing the primitive modules."
  libdirPrim <- useTC stPrimitiveLibDir
  reportSLn "import.main" 20 $ "Library primitive dir = " ++ show libdirPrim
  -- Turn off import-chasing messages.
  -- We have to modify the persistent verbosity setting, since
  -- getInterface resets the current verbosity settings to the persistent ones.

  bracket_ (getsTC Lens.getPersistentVerbosity) Lens.putPersistentVerbosity $ do
    -- set root verbosity to 0
    Lens.modifyPersistentVerbosity
      (Strict.Just . Trie.insert [] 0 . Strict.fromMaybe Trie.empty)

    -- We don't want to generate highlighting information for Agda.Primitive.
    withHighlightingLevel None $
      forM_ (map (filePath libdirPrim </>) $ Set.toList primitiveModules) \ f -> do
        sf <- srcFromPath (mkAbsolute f)
        primSource <- parseSource sf
        checkModuleName' (srcModuleName primSource) (srcOrigin primSource)
        void $ getNonMainInterface (srcModuleName primSource) (Just primSource)

  reportSLn "import.main" 10 $ "Done importing the primitive modules."

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
  mi <- getNonMainModuleInfo x msrc
  tcWarningsToError (TopLevelModuleNameWithSourceFile x $ miSourceFile mi) $ Set.toAscList $ miWarnings mi
  return (miInterface mi)

getNonMainModuleInfo
  :: TopLevelModuleName
  -> Maybe Source
     -- ^ Optional: the source code and some information about the source code.
  -> TCM ModuleInfo
getNonMainModuleInfo x msrc =
  -- Preserve/restore the current pragma options, which will be mutated when loading
  -- and checking the interface.
  bracket_ (useTC stPragmaOptions) (stPragmaOptions `setTCLens`) $
           getInterface x NotMainInterface msrc

-- | If the module has already been visited (without warnings), then
-- its interface is returned directly.
--
-- Otherwise the interface is loaded via 'getStoredInterface'.
--
-- If that fails it is created via 'createInterface' or, for non-main modules,
-- 'createInterfaceIsolated'.
-- A such created interface is stored for potential later use.

getInterface
  :: TopLevelModuleName
  -> MainInterface
  -> Maybe Source
     -- ^ Optional: the source code and some information about the source code.
  -> TCM ModuleInfo
getInterface x isMain msrc = locallyTC eImportStack (x :) do

  -- We remember but reset the pragma options locally.
  currentOptions <- useTC stPragmaOptions
  -- Issue #3644 (Abel 2020-05-08): Set approximate range for errors in options.
  setCurrentRange (C.modPragmas . srcModule <$> msrc) $ do
    -- Now reset the options
    setCommandLineOptions =<< getsTC (stPersistentOptions . stPersistentState)

  -- Lookup x in the collection of visited modules.
  getVisitedModule x >>= \case

    -- Case: already visited and usable.
    Just mi
        -- We can only reuse a sufficiently checked module,
        -- e.g. we cannot import a just scope-checked module when type-checking a module.
      | miMode mi >= mode
        -- A module with warnings should never be allowed to be imported from another module.
      , null $ miWarnings mi -> do
          reportSLn "import.visit" 10 $ "  Already visited " ++ prettyShow x
          addOptionsCompatibilityWarnings currentOptions mi

    -- Case: not already visited or unusable.
    _ -> do

      -- Load the module.
      reportSLn "import.visit" 5 $ "  Getting interface for " ++ prettyShow x

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
          modifyTCLens stModuleToSourceId $ Map.insert x file
          pure file

      reportSDoc "import.iface" 15 do
        path <- srcFilePath file
        P.text $ List.intercalate "\n" $ map ("  " ++)
          [ "module: " ++ prettyShow x
          , "file:   " ++ prettyShow path
          ]

      reportSLn "import.iface" 15 $ "  Check for cycle"
      checkForImportCycle

      mi <- Bench.billTo [Bench.Import] (getStoredInterface x file msrc)
        `catchExceptT` \ reason -> do

            reportSLn "import.iface" 5 $ concat ["  ", prettyShow x, " is not up-to-date because ", reason, "."]
            setCommandLineOptions . stPersistentOptions . stPersistentState =<< getTC
            mi <- case isMain of
              MainInterface _ -> createInterface x file isMain msrc
              NotMainInterface -> createInterfaceIsolated x file msrc

            -- Ensure that the given module name matches the one in the file.
            let topLevelName = iTopLevelModuleName (miInterface mi)
            unless (topLevelName == x) do
              path <- srcFilePath file
              typeError $ OverlappingProjects path topLevelName x

            pure mi

      mi <- addOptionsCompatibilityWarnings currentOptions mi
      reportSLn "import.visit" 5 $ "  Now we've looked at " ++ prettyShow x

      -- Interfaces are not stored if we are only scope-checking, or
      -- if any warnings were encountered.
      when (mode == ModuleTypeChecked && null (miWarnings mi)) do
        storeDecodedModule mi

      reportS "warning.import" 10
        [ "module: " ++ show (moduleNameParts x)
        , "WarningOnImport: " ++ show (iImportWarning (miInterface mi))
        ]

      -- Record the module as visited.
      visitModule mi
      return mi
  where
    mode :: ModuleCheckMode
    mode = case isMain of
      MainInterface TypeCheck  -> ModuleTypeChecked
      NotMainInterface         -> ModuleTypeChecked
      MainInterface ScopeCheck -> ModuleScopeChecked

    addOptionsCompatibilityWarnings :: PragmaOptions -> ModuleInfo -> TCM ModuleInfo
    addOptionsCompatibilityWarnings currentOptions
      mi@ModuleInfo{ miInterface = i, miPrimitive = isPrim, miWarnings = ws } = do

      -- Check that imported options are compatible with current ones (issue #2487),
      -- but give primitive modules a pass.
      -- Compute updated warnings if needed.
      ws' <- fromMaybe ws <$> getOptionsCompatibilityWarnings isMain isPrim currentOptions i
      return mi{ miWarnings = ws' }

-- | If checking produced non-benign warnings, error out.
--
raiseNonFatalErrors :: (HasOptions m, MonadTCError m)
  => CheckResult  -- ^ E.g. obtained from 'typeCheckMain'.
  -> m ()
raiseNonFatalErrors result = do
  Set1.unlessNullM (applyFlagsToTCWarnings (crWarnings result)) $ \ ws ->
    typeError $ NonFatalErrors ws

-- | Check if the options used for checking an imported module are
--   compatible with the current options. Raises Non-fatal errors if
--   not.
checkOptionsCompatible ::
  PragmaOptions -> PragmaOptions -> TopLevelModuleName -> TCM Bool
checkOptionsCompatible current imported importedModule = flip execStateT True $ do
  reportSDoc "import.iface.options" 25 $ P.nest 2 $ "current options  =" P.<+> showOptions current
  reportSDoc "import.iface.options" 25 $ P.nest 2 $ "imported options =" P.<+> showOptions imported
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

getOptionsCompatibilityWarnings ::
     MainInterface
  -> Bool           -- ^ Are we looking at a primitvie module?
  -> PragmaOptions
  -> Interface
  -> TCM (Maybe (Set TCWarning))
getOptionsCompatibilityWarnings isMain False currentOptions Interface{ iOptionsUsed, iTopLevelModuleName } = do
  ifM (checkOptionsCompatible currentOptions iOptionsUsed iTopLevelModuleName)
    {-then-} (return Nothing) -- No warnings to collect because options were compatible.
    {-else-} (Just <$> getAllWarnings' isMain ErrorWarnings)
-- Options consistency checking is disabled for always-available primitive modules.
getOptionsCompatibilityWarnings _ True _ _ = return Nothing

-- | Try to get the interface from interface file or cache.

getStoredInterface :: HasCallStack
  => TopLevelModuleName
     -- ^ Module name of file we process.
  -> SourceFile
     -- ^ File we process.
  -> Maybe Source
  -> ExceptT String TCM ModuleInfo
getStoredInterface x file@(SourceFile fi) msrc = do

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
                    Nothing -> do
                      path <- srcFilePath file
                      liftIO $ hashTextFile path
                    Just src -> return $ hashText (srcText src)

        unless (sourceH == ifaceH) $
          throwError $ concat
            [ "the source hash (", show sourceH, ")"
            , " does not match the source hash for the interface (", show ifaceH, ")"
            ]

        reportSLn "import.iface" 5 $ concat ["  ", prettyShow x, " is up-to-date."]

  let
    -- Load or reload the interface file, if possible.
    loadInterfaceFile whyNotCached =
      withExceptT (\e -> concat [whyNotCached, " and ", e]) $ do
      whenM ignoreAllInterfaces $
        throwError "we're ignoring all interface files"

      whenM ignoreInterfaces $
        whenNothingM (isBuiltinModule fi) $
            throwError "we're ignoring non-builtin interface files"

      (ifile, hashes) <- getIFileHashesET

      let ifp = filePath $ intFilePath $ ifile

      Bench.billTo [Bench.Deserialization] $ do
        checkSourceHashET (fst hashes)

        reportSLn "import.iface" 5 $ "  no stored version, reading " ++ ifp

        i <- maybeToExceptT "bad interface, re-type checking" $ MaybeT $
          readInterface ifile

        -- Ensure that the given module name matches the one in the file.
        let topLevelName = iTopLevelModuleName i
        unless (topLevelName == x) do
          path <- srcFilePath file
          lift $ typeError $ OverlappingProjects path topLevelName x

        isPrimitiveMod <- isPrimitiveModule fi

        lift $ chaseMsg "Loading " x $ Just ifp
        -- print imported warnings
        reportWarningsForModule x $ iWarnings i

        loadDecodedModule file $ ModuleInfo
          { miInterface = i
          , miWarnings = empty
          , miPrimitive = isPrimitiveMod
          , miMode = ModuleTypeChecked
          , miSourceFile = file
          }

  -- Check if we have cached the module.
  cachedE <- runExceptT $ maybeToExceptT "the interface has not been decoded" $ MaybeT $
      lift $ getDecodedModule x

  case cachedE of
    Left whyNotCached -> loadInterfaceFile whyNotCached

    -- If it's cached ignoreInterfaces has no effect;
    -- to avoid typechecking a file more than once.
    Right mi -> do
      (ifile, hashes) <- getIFileHashesET

      let ifp = filePath $ intFilePath ifile
      let i = miInterface mi

      -- Make sure the hashes match.
      let cachedIfaceHash = iFullHash i
      let fileIfaceHash = snd hashes
      if cachedIfaceHash /= fileIfaceHash then do
        lift $ dropDecodedModule x
        reportSLn "import.iface" 50 $ "  cached hash = " ++ show cachedIfaceHash
        reportSLn "import.iface" 50 $ "  stored hash = " ++ show fileIfaceHash
        reportSLn "import.iface" 5 $ "  file is newer, re-reading " ++ ifp
        loadInterfaceFile $ concat
          [ "the cached interface hash (", show cachedIfaceHash, ")"
          , " does not match interface file (", show fileIfaceHash, ")"
          ]
       else Bench.billTo [Bench.Deserialization] $ do
        checkSourceHashET (iSourceHash i)

        reportSLn "import.iface" 5 $ "  using stored version of " ++ filePath (intFilePath ifile)
        loadDecodedModule file mi

-- | Report those given warnings that come from the given module.

reportWarningsForModule :: MonadDebug m => TopLevelModuleName -> Set TCWarning -> m ()
reportWarningsForModule x warns = do
  unlessNull (filter ((Strict.Just (Just x) ==) . fmap rangeFileName . tcWarningOrigin) $ Set.toAscList warns) \ ws ->
    alwaysReportSDoc "warning" 1 $
      -- Andreas, 2025-08-01, PR #8040
      -- Make sure that imported warnings coming from different modules are separated by an empty line.
      -- E.g. test/Succeed/ImportWarnings
      -- Technique from PR #7473:
      P.vcat $ concatMap (\ w -> [ "", P.prettyTCM w ]) ws
      -- Technique from PR #7362:
      -- P.vsep $ map P.prettyTCM ws

-- | Check whether the loaded module is up-to-date
--   and merge into state if this is the case.
--
loadDecodedModule
  :: SourceFile
     -- ^ File we process.
  -> ModuleInfo
     -- ^ The interface we loaded or created.
  -> ExceptT String TCM ModuleInfo
loadDecodedModule sf@(SourceFile fi) mi = do
  file <- srcFilePath sf
  let fp      = filePath file
  let i       = miInterface mi
  let imports = iImportedModules i
  let name    = iTopLevelModuleName i

  -- Print imported modules.
  verboseS "import.iface.imports" 5 $ unless (null imports) $
    reportSLn "import.iface.imports" 5 $ intercalate "\n" $
      unwords [ prettyShow name, "imports:" ] :
      map (\ (x, hash) -> unwords [ " ", "-", prettyShow x, concat ["(hash: ", prettyShow hash, ")"] ])
        imports

  -- We set the pragma options of the skipped file here, so that
  -- we can check that they are compatible with those of the
  -- imported modules. Also, if the top-level file is skipped we
  -- want the pragmas to apply to interactive commands in the UI.
  -- Jesper, 2021-04-18: Check for changed options in library files!
  -- (see #5250)
  libOptions <- lift $ getLibraryOptions file name
  lift $ mapM_ setOptionsFromPragma (libOptions ++ iFilePragmaOptions i)

  -- Check that options that matter haven't changed compared to
  -- current options (issue #2487).
  whenNothingM (isBuiltinModule fi) do
    current <- useTC stPragmaOptions
    when (recheckBecausePragmaOptionsChanged (iOptionsUsed i) current) $
      throwError "options changed"

  -- If any of the imports are newer we need to re-typecheck.
  badHashMessages <- fmap lefts $ forM imports \ (impName, impHash) -> runExceptT do
    reportSLn "import.iface" 30 $ concat ["Checking that module hash of import ", prettyShow impName, " matches ", prettyShow impHash ]
    latestImpHash <- lift $ lift $ setCurrentRange impName $ moduleHash impName
    reportSLn "import.iface" 30 $ concat ["Done checking module hash of import ", prettyShow impName]
    when (impHash /= latestImpHash) $
      throwError $ concat
        [ "module hash for imported module ", prettyShow impName, " is out of date"
        , " (import cached=", prettyShow impHash, ", latest=", prettyShow latestImpHash, ")"
        ]

  unlessNull badHashMessages (throwError . unlines)

  reportSLn "import.iface" 5 $ prettyShow name ++ ": interface is valid and can be merged into the state."

  lift $ mergeInterface i
  Bench.billTo [Bench.Highlighting] $
    lift $ ifTopLevelAndHighlightingLevelIs NonInteractive $
      highlightFromInterface i sf

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

      ms          <- asksTC envImportStack
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
      -- Every interface is treated in isolation. Note: Some changes to
      -- the persistent state may not be preserved if an error other
      -- than a type error or an IO exception is encountered in an
      -- imported module.
      (mi, newModToSource, newDecodedModules) <- (either throwError pure =<<) $
           withoutCache $
           -- The cache should not be used for an imported module, and it
           -- should be restored after the module has been type-checked
           freshTCM $
             localTC (\e -> e
                              -- Andreas, 2014-08-18:
                              -- Preserve the range of import statement
                              -- for reporting termination errors in
                              -- imported modules:
                            { envRange              = range
                            , envCall               = call
                            , envImportStack        = ms
                            }) $ do
               setDecodedModules ds
               setCommandLineOptions opts
               stModuleToSource `setTCLens` mf
               setVisitedModules vs
               addImportedThings isig metas ibuiltin ipatsyns display
                 userwarn partialdefs empty opaqueblk opaqueid

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
  indentation <- (`replicate` ' ') <$> asksTC (pred . length . envImportStack)
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
highlightFromInterface i sf = do
  reportSDoc "import.iface" 5 do
    file <- srcFilePath sf
    P.text $ "Generating syntax info for " ++ filePath file ++
      " (read from interface)."
  printHighlightingInfo KeepHighlighting (iHighlighting i)

-- | Read interface file corresponding to a module.

readInterface :: InterfaceFile -> TCM (Maybe Interface)
readInterface file = do
    let ifp = filePath $ intFilePath file
    bstr <- (liftIO $ Just <$!> B.readFile ifp) `catchError` \case
      IOException _ _ e -> do
        alwaysReportSLn "" 0 $ "IO exception: " ++ show e
        return Nothing   -- Work-around for file locking bug.
                         -- TODO: What does this refer to? Please
                         -- document.
      e -> throwError e
    case bstr of
      Just bstr -> runMaybeT (constructIScope <$!> decodeInterface bstr)
      Nothing   -> pure Nothing


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
    let
      filteredIface = i { iInsideScope = withoutPrivates $ iInsideScope i }
    filteredIface <- pruneTemporaryInstances filteredIface
    reportSLn "import.iface.write" 50 $
      "Writing interface file with hash " ++ show (iFullHash filteredIface) ++ "."
    iface <- encodeFile fp filteredIface
    reportSLn "import.iface.write" 5 "Wrote interface file."
    pure iface
  `catchError` \e -> do
    alwaysReportSLn "" 1 $
      "Failed to write interface " ++ fp ++ "."
    -- Andreas, 2025-09-12, issue #8098, don't delete when writing failed on a readonly file.
    -- Only delete file when disk is full or Agda had an internal error during serialization.
    case e of
      IOException _ _ ioe | not (isUserError ioe), not (isFullError ioe)
        -> return ()
      _ -> liftIO $ whenM (doesFileExist fp) $ removeFile fp
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
createInterface mname sf@(SourceFile sfi) isMain msrc = do
  file <- srcFilePath sf
  let fp = filePath file
  let checkMsg = case isMain of
                   MainInterface ScopeCheck -> "Reading "
                   _                        -> "Checking"
      withMsgs = bracket_
       (chaseMsg checkMsg mname $ Just fp)
       (const $ do ws <- getAllWarnings AllWarnings
                   let classified = classifyWarnings $ Set.toAscList ws
                   reportWarningsForModule mname $ tcWarnings classified
                   when (null (nonFatalErrors classified)) $ chaseMsg "Finished" mname Nothing)

  withMsgs $
    Bench.billTo [Bench.TopModule mname] $
    localTC (\ e -> e { envCurrentPath = Just sfi }) do

    let onlyScope = isMain == MainInterface ScopeCheck

    reportSLn "import.iface.create" 5 $
      "Creating interface for " ++ prettyShow mname ++ "..."
    verboseS "import.iface.create" 10 $ do
      visited <- prettyShow <$> getPrettyVisitedModules
      reportSLn "import.iface.create" 10 $ "  visited: " ++ visited

    src <- maybe (parseSource sf) pure msrc

    srcPath <- srcFilePath $ srcOrigin src

    fileTokenInfo <- Bench.billTo [Bench.Highlighting] $
      generateTokenInfoFromSource
        (let !top = srcModuleName src in
         mkRangeFile srcPath (Just top))
        (TL.unpack $ srcText src)
    stTokens `modifyTCLens` (fileTokenInfo <>)

    -- Only check consistency if not main (we check consistency for the main module in
    -- `typeCheckMain`.
    let checkConsistency | MainInterface{} <- isMain = False
                         | otherwise                 = True
    setOptionsFromSourcePragmas checkConsistency src
    checkAttributes (srcAttributes src)
    syntactic <- optSyntacticEquality <$> pragmaOptions
    localTC (\env -> env { envSyntacticEqualityFuel = syntactic }) $ do

    verboseS "import.iface.create" 15 $ do
      nestingLevel      <- asksTC (pred . length . envImportStack)
      highlightingLevel <- asksTC envHighlightingLevel
      reportSLn "import.iface.create" 15 $ unlines
        [ "  nesting      level: " ++ show nestingLevel
        , "  highlighting level: " ++ show highlightingLevel
        ]

    -- Scope checking.
    reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": Starting scope checking."
    topLevel <- Bench.billTo [Bench.Scoping] $ do
      let topDecls = C.modDecls $ srcModule src
      concreteToAbstract_ (TopLevel (srcOrigin src) mname topDecls)
    reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": Finished scope checking."

    let ds    = topLevelDecls topLevel
        scope = topLevelScope topLevel

    -- Highlighting from scope checker.
    reportSLn "import.iface.highlight" 15 $ prettyShow mname ++ ": Starting highlighting from scope."
    Bench.billTo [Bench.Highlighting] $ do
      -- Generate and print approximate syntax highlighting info.
      ifTopLevelAndHighlightingLevelIs NonInteractive $
        printHighlightingInfo KeepHighlighting fileTokenInfo
      ifTopLevelAndHighlightingLevelIsOr NonInteractive onlyScope $
        mapM_ (\ d -> generateAndPrintSyntaxInfo d Partial onlyScope) ds
    reportSLn "import.iface.highlight" 15 $ prettyShow mname ++ ": Finished highlighting from scope."


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
        reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": Skipping type checking."
        cacheCurrentLog
      else do
        reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": Starting type checking."
        Bench.billTo [Bench.Typing] $ mapM_ checkDeclCached ds `finally_` cacheCurrentLog
        reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": Finished type checking."

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
      tickN "metas" (metaId m)

    -- Highlighting from type checker.
    reportSLn "import.iface.highlight" 15 $ prettyShow mname ++ ": Starting highlighting from type info."
    Bench.billTo [Bench.Highlighting] $ do

      -- Move any remaining token highlighting to stSyntaxInfo.
      toks <- useTC stTokens
      ifTopLevelAndHighlightingLevelIs NonInteractive $
        printHighlightingInfo KeepHighlighting toks
      stTokens `setTCLens` mempty

      -- Grabbing warnings and unsolved metas to highlight them
      warnings <- getAllWarnings AllWarnings
      unless (null warnings) $ reportSDoc "import.iface.highlight" 20 $
        "collected warnings: " <> prettyTCM warnings
      unsolved <- getAllUnsolvedWarnings
      unless (null unsolved) $ reportSDoc "import.iface.highlight" 20 $
        "collected unsolved: " <> prettyTCM unsolved
      let warningInfo =
            Highlighting.convert $ foldMap warningHighlighting $ Set.fromList unsolved `Set.union` warnings

      stSyntaxInfo `modifyTCLens` \inf -> (inf `mappend` toks) `mappend` warningInfo

      whenM (optGenerateVimFile <$> commandLineOptions) $
        -- Generate Vim file.
        evalWithScope scope $ generateVimFile $ filePath $ srcPath
    reportSLn "import.iface.create" 15 $ prettyShow mname ++ ": Finished highlighting from type info."

    setScope scope
    reportSLn "scope.top" 90 $ "SCOPE " ++ show scope

    -- TODO: It would be nice if unsolved things were highlighted
    -- after every mutual block.

    openMetas <- getOpenMetas
    unless (null openMetas) $ do
      reportSLn "import.metas" 10 $ prettyShow mname ++ ": We have unsolved metas."
      reportSDoc "import.metas" 10 $ prettyGoals =<< getGoals

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
        reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": Turning unsolved metas (if any) into postulates."
        withCurrentModule (scope ^. scopeCurrent) openMetasToPostulates
        -- Clear constraints as they might refer to what
        -- they think are open metas.
        stAwakeConstraints    `setTCLens` []
        stSleepingConstraints `setTCLens` []

    -- Serialization.
    reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": Starting serialization."
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
    reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": Finished serialization."

    mallWarnings <- getAllWarnings' isMain ErrorWarnings

    isWritingInterfaces <- writeInterfaces

    reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": Considering writing to interface file."
    finalIface <- constructIScope <$> case (null mallWarnings, isMain, isWritingInterfaces) of
      (False, _, _) -> do
        -- Andreas, 2018-11-15, re issue #3393
        -- The following is not sufficient to fix #3393
        -- since the replacement of metas by postulates did not happen.
        -- -- | not (allowUnsolved && all (isUnsolvedWarning . tcWarning) allWarnings) -> do
        reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": We have warnings, skipping writing interface file."
        return i
      (True, MainInterface ScopeCheck , _) -> do
        reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": We are just scope-checking, skipping writing interface file."
        return i
      (_, _, False) -> do
        reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": We are not writing any interfaces, skipping writing interface file."
        return i
      (True, _, _) -> Bench.billTo [Bench.Serialization] $ do
        reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": Actually calling writeInterface."
        -- The file was successfully type-checked (and no warnings were
        -- encountered), so the interface should be written out.
        ifile <- toIFile sf
        serializedIface <- writeInterface ifile i
        reportSLn "import.iface.create" 7 $ prettyShow mname ++ ": Finished writing to interface file."
        pure serializedIface

    -- -- Restore the open metas, as we might continue in interaction mode.
    -- Actually, we do not serialize the metas if checking the MainInterface
    -- stMetaStore `setTCLens` savedMetaStore

    -- Profiling: Print statistics.
    printStatistics (Just mname) =<< getStatistics

    -- Get the statistics of the current module
    -- and add it to the accumulated statistics.
    localStatistics <- getStatistics
    lensAccumStatistics `modifyTCLens'` (<>) localStatistics
    reportSLn "import.iface" 25 $ prettyShow mname ++ ": Added statistics to the accumulated statistics."

    isPrimitiveMod <- isPrimitiveModule sfi

    return ModuleInfo
      { miInterface = finalIface
      , miWarnings = mallWarnings
      , miPrimitive = isPrimitiveMod
      , miMode = moduleCheckMode isMain
      , miSourceFile = sf
      }

-- | Expert version of 'getAllWarnings'; if 'isMain' is a
-- 'MainInterface', the warnings definitely include also unsolved
-- warnings.

getAllWarnings' :: (ReadTCState m, MonadWarning m, MonadTCM m) => MainInterface -> WhichWarnings -> m (Set TCWarning)
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
--   have been successfully type checked.
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
    !mhs <- mapM (\top -> (top,) <$> moduleHash top) . Set.toAscList =<< useR stImportedModules
    !foreignCode <- useTC stForeignCode

    let !scope = topLevelScope topLevel

    (!solvedMetas, !definitions, !displayForms) <- eliminateDeadCode scope
    !sig <- set sigDefinitions definitions <$> getSignature

    -- Andreas, 2015-02-09 kill ranges in pattern synonyms before
    -- serialization to avoid error locations pointing to external files
    -- when expanding a pattern synonym.
    !patsyns <- killRange <$> getPatternSyns

    !userwarns   <- useTC stLocalUserWarnings
    !importwarn  <- useTC stWarningOnImport
    !syntaxInfo  <- useTC stSyntaxInfo
    !optionsUsed <- useTC stPragmaOptions
    !partialDefs <- useTC stLocalPartialDefs

    -- Only serialise the opaque blocks actually defined in this
    -- top-level module.
    !opaqueBlocks' <- useTC stOpaqueBlocks
    !opaqueIds' <- useTC stOpaqueIds
    let
      !mh = moduleNameId (srcModuleName src)
      !opaqueBlocks = Map.filterWithKey (\(OpaqueId _ mod) _ -> mod == mh) opaqueBlocks'
      isLocal qnm = case nameId (qnameName qnm) of
        NameId _ mh' -> mh' == mh
      !opaqueIds = Map.filterWithKey (\qnm (OpaqueId _ mod) -> isLocal qnm || mod == mh) opaqueIds'

    !builtin  <- Map.mapWithKey (\ x b -> primName x <$> b) <$> useTC stLocalBuiltins
    !warnings <- Set.filter (isSourceCodeWarning . warningName . tcWarning) <$> getAllWarnings AllWarnings

    let !i = Interface
          { iSourceHash           = hashText source
          , iSource               = source
          , iFileType             = fileType
          , iImportedModules      = mhs
          , iModuleName           = mname
          , iTopLevelModuleName   = srcModuleName src
          , iScope                = empty -- publicModules scope
          , iInsideScope          = scope
          , iSignature            = sig
          , iMetaBindings         = solvedMetas
          , iDisplayForms         = displayForms
          , iUserWarnings         = userwarns
          , iImportWarning        = importwarn
          , iBuiltin              = builtin
          , iForeignCode          = foreignCode
          , iHighlighting         = syntaxInfo
          , iDefaultPragmaOptions = defPragmas
          , iFilePragmaOptions    = filePragmas
          , iOptionsUsed          = optionsUsed
          , iPatternSyns          = patsyns
          , iWarnings             = warnings
          , iPartialDefs          = partialDefs
          , iOpaqueBlocks         = opaqueBlocks
          , iOpaqueNames          = opaqueIds
          }
    !i <-
      ifM (optSaveMetas <$> pragmaOptions)
        (return i)
        (do reportSLn "import.iface" 7
              "  instantiating all metavariables in interface"
            Bench.billTo [Bench.InterfaceInstantiateFull] $ liftReduce $ instantiateFull' i)
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
  h    <- openBinaryFile ifile ReadMode
  bstr <- B.hGetSome h (2 * hashSize)
  hClose h
  deserializeHashes bstr

moduleHash :: TopLevelModuleName -> TCM Hash
moduleHash m = iFullHash <$> getNonMainInterface m Nothing
