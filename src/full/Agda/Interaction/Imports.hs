{-# LANGUAGE CPP #-}
{-| This module deals with finding imported modules and loading their
    interface files.
-}
module Agda.Interaction.Imports where

import Prelude hiding (catch)

import Control.Monad.Error
import Control.Monad.State
import qualified Control.Exception as E
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.ByteString.Lazy as BS
import Data.List
import Data.Maybe
import Data.Map (Map)
import Data.Set (Set)
import System.Directory
import System.Time
import qualified Agda.Utils.IO.Locale as LocIO
import System.FilePath hiding (splitPath)

import Agda.Syntax.Position
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as C
import Agda.Syntax.Abstract.Name
import Agda.Syntax.Parser
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Internal

import Agda.Termination.TermCheck

import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Serialise
import Agda.TypeChecking.Primitive
import Agda.TypeChecker

import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Interaction.Highlighting.Precise (HighlightingInfo)
import Agda.Interaction.Highlighting.Generate
import Agda.Interaction.Highlighting.Vim
import qualified Agda.Interaction.Highlighting.Range as R

import Agda.Utils.FileName
import Agda.Utils.Monad
import Agda.Utils.IO.Binary
import Agda.Utils.Pretty

import Agda.Utils.Impossible
#include "../undefined.h"

-- | Merge an interface into the current proof state.
mergeInterface :: Interface -> TCM ()
mergeInterface i = do
    let sig	= iSignature i
	builtin = Map.toList $ iBuiltin i
	prim	= [ x | (_,Prim x) <- builtin ]
	bi	= Map.fromList [ (x,Builtin t) | (x,Builtin t) <- builtin ]
    bs <- getBuiltinThings
    reportSLn "import.iface.merge" 10 $ "Merging interface"
    reportSLn "import.iface.merge" 20 $
      "  Current builtins " ++ show (Map.keys bs) ++ "\n" ++
      "  New builtins     " ++ show (Map.keys bi)
    case Map.toList $ Map.intersection bs bi of
      []               -> return ()
      (b, Builtin x):_ -> typeError $ DuplicateBuiltinBinding b x x
      (_, Prim{}):_    -> __IMPOSSIBLE__
    addImportedThings sig bi (iHaskellImports i)
    reportSLn "import.iface.merge" 20 $
      "  Rebinding primitives " ++ show prim
    prim <- Map.fromList <$> mapM rebind prim
    modify $ \st -> st { stImportedBuiltins = stImportedBuiltins st `Map.union` prim
		       }
    where
	rebind x = do
	    PrimImpl _ pf <- lookupPrimitiveFunction x
	    return (x, Prim pf)

addImportedThings ::
  Signature -> BuiltinThings PrimFun -> Set String -> TCM ()
addImportedThings isig ibuiltin hsImports =
  modify $ \st -> st
    { stImports          = unionSignatures [stImports st, isig]
    , stImportedBuiltins = Map.union (stImportedBuiltins st) ibuiltin
    , stHaskellImports   = Set.union (stHaskellImports st) hsImports
    }

-- | Scope checks the given module. A proper version of the module
-- name (with correct definition sites) is returned.

scopeCheckImport :: ModuleName -> TCM (ModuleName, Map ModuleName Scope)
scopeCheckImport x = do
    reportSLn "import.scope" 5 $ "Scope checking " ++ show x
    verboseS "import.scope" 10 $ do
      visited <- Map.keys <$> getVisitedModules
      liftIO $ LocIO.putStrLn $
        "  visited: " ++ intercalate ", " (map (render . pretty) visited)
    i <- fst <$> getInterface x
    addImport x
    return (iModuleName i `withRangesOfQ` mnameToConcrete x, iScope i)

-- | If the module has already been visited (without warnings), then
-- its interface is returned directly. Otherwise the computation is
-- used to find the interface and the computed interface is stored for
-- potential later use.

alreadyVisited :: C.TopLevelModuleName ->
                  TCM (Interface, Either Warnings ClockTime) ->
                  TCM (Interface, Either Warnings ClockTime)
alreadyVisited x getIface = do
    mm <- getVisitedModule x
    case mm of
        -- A module with warnings should never be allowed to be
        -- imported from another module.
	Just mi | not (miWarnings mi) -> do
          reportSLn "import.visit" 10 $ "  Already visited " ++ render (pretty x)
          return (miInterface mi, Right $ miTimeStamp mi)
	_ -> do
          reportSLn "import.visit" 5 $ "  Getting interface for " ++ render (pretty x)
          r@(i, wt) <- getIface
          reportSLn "import.visit" 5 $ "  Now we've looked at " ++ render (pretty x)
          case wt of
            Left _ -> do
              t <- liftIO getClockTime
              visitModule $ ModuleInfo
                { miInterface  = i
                , miWarnings   = True
                , miTimeStamp  = t
                }
            Right t ->
              visitModule $ ModuleInfo
                { miInterface  = i
                , miWarnings   = False
                , miTimeStamp  = t
                }
          return r

-- | Warnings.
--
-- Invariant: The fields are never empty at the same time.

data Warnings = Warnings
  { terminationProblems   :: [([QName], [R.Range])]
    -- ^ Termination checking problems are not reported if
    -- 'optTerminationCheck' is 'False'.
  , unsolvedMetaVariables :: [Range]
    -- ^ Meta-variable problems are reported as type errors unless
    -- 'optAllowUnsolved' is 'True'.
  , unsolvedConstraints   :: Constraints
    -- ^ Same as 'unsolvedMetaVariables'.
  }

-- | Turns warnings into an error. Even if several errors are possible
-- only one is raised.

warningsToError :: Warnings -> TypeError
warningsToError (Warnings [] [] [])    = __IMPOSSIBLE__
warningsToError (Warnings _ w@(_:_) _) = UnsolvedMetas w
warningsToError (Warnings _ _ w@(_:_)) = UnsolvedConstraints w
warningsToError (Warnings w@(_:_) _ _) = TerminationCheckFailed w

-- | Type checks the given module (if necessary).

typeCheck :: AbsolutePath -> TCM (Interface, Maybe Warnings)
typeCheck f = do
  m <- moduleName f

  (i, wt) <- getInterface' m True
  return (i, case wt of
    Left w  -> Just w
    Right _ -> Nothing)

-- | Tries to return the interface associated to the given module. The
-- time stamp of the relevant interface file is also returned. May
-- type check the module. An error is raised if a warning is
-- encountered.

getInterface :: ModuleName -> TCM (Interface, ClockTime)
getInterface x = do
  (i, wt) <- getInterface' (toTopLevelModuleName x) False
  case wt of
    Left  w -> typeError $ warningsToError w
    Right t -> return (i, t)

-- | A more precise variant of 'getInterface'. If warnings are
-- encountered then they are returned instead of being turned into
-- errors.

getInterface' :: C.TopLevelModuleName
              -> Bool  -- ^ If type checking is necessary, should all
                       -- state changes inflicted by 'createInterface'
                       -- be preserved?
              -> TCM (Interface, Either Warnings ClockTime)
getInterface' x includeStateChanges =
  -- Preserve the pragma options unless includeStateChanges is True.
  bracket (stPragmaOptions <$> get)
          (unless includeStateChanges . setPragmaOptions) $ \_ -> do
   -- Forget the pragma options (locally).
   setCommandLineOptions . stPersistentOptions =<< get

   alreadyVisited x $ addImportCycleCheck x $ do
    file <- findFile x  -- requires source to exist

    reportSLn "import.iface" 10 $ "  Check for cycle"
    checkForImportCycle

    uptodate <- ifM ignoreInterfaces
		    (return False)
		    (liftIO $ filePath (toIFile file)
                                `isNewerThan`
                              filePath file)

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
    unless (visited || stateChangesIncluded) $ mergeInterface i

    modify (\s -> s { stCurrentModule = Just $ iModuleName i })

    -- Interfaces are only stored if no warnings were encountered.
    case wt of
      Left  w -> return ()
      Right t -> storeDecodedModule i t

    return (i, wt)

    where
	skip file = do
	    -- Examine the mtime of the interface file. If it is newer than the
	    -- stored version (in stDecodedModules), or if there is no stored version,
	    -- read and decode it. Otherwise use the stored version.
            let ifile = filePath $ toIFile file
	    t            <- liftIO $ getModificationTime ifile
	    mm           <- getDecodedModule x
	    (cached, mi) <- case mm of
		      Just (mi, mt) ->
			 if mt < t
			 then do dropDecodedModule x
				 reportSLn "import.iface" 5 $ "  file is newer, re-reading " ++ ifile
				 (,) False <$> readInterface ifile
			 else do reportSLn "import.iface" 5 $ "  using stored version of " ++ ifile
				 return (True, Just mi)
		      Nothing ->
			 do reportSLn "import.iface" 5 $ "  no stored version, reading " ++ ifile
			    (,) False <$> readInterface ifile

	    -- Check that it's the right version
	    case mi of
		Nothing	-> do
		    reportSLn "import.iface" 5 $ "  bad interface, re-type checking"
		    typeCheck file
		Just i	-> do

		    reportSLn "import.iface" 5 $ "  imports: " ++ show (iImportedModules i)

		    ts <- map snd <$> mapM getInterface (iImportedModules i)

		    -- If any of the imports are newer we need to retype check
		    if any (> t) ts
			then do
			    -- liftIO close	-- Close the interface file. See above.
			    typeCheck file
			else do
			    reportSLn "" 1 $
                              "Skipping " ++ render (pretty x) ++
                                " (" ++ (if cached then "cached" else ifile) ++ ")."
                            -- We set the pragma options of the skipped file here,
                            -- because if the top-level file is skipped we want the
                            -- pragmas to apply to interactive commands in the UI.
                            mapM_ setOptionsFromPragma (iPragmaOptions i)
			    return (False, (i, Right t))

	typeCheck file = do
	    -- Do the type checking.
            reportSLn "" 1 $ "Checking " ++ render (pretty x) ++ " (" ++ filePath file ++ ")."
            if includeStateChanges then do
              r <- createInterface file x

              -- Merge the signature with the signature for imported
              -- things.
              sig <- getSignature
              addImportedThings sig Map.empty Set.empty
              setSignature emptySignature

              return (True, r)
             else do
              ms       <- getImportPath
              mf       <- stModuleToSource <$> get
              vs       <- getVisitedModules
              ds       <- getDecodedModules
              opts     <- stPersistentOptions <$> get
              isig     <- getImportedSignature
              ibuiltin <- gets stImportedBuiltins
              -- Every interface is treated in isolation.
              r <- liftIO $ runTCM $
                     withImportPath ms $ do
                       setDecodedModules ds
                       setCommandLineOptions opts
                       modify $ \s -> s { stModuleToSource = mf }
                       setVisitedModules vs
                       addImportedThings isig ibuiltin Set.empty

                       r <- createInterface file x

                       mf        <- stModuleToSource <$> get
                       vs        <- getVisitedModules
                       ds        <- getDecodedModules
                       isig      <- getImportedSignature
                       ibuiltin  <- gets stImportedBuiltins
                       hsImports <- getHaskellImports
                       return (r, do
                         modify $ \s -> s { stModuleToSource = mf }
                         setVisitedModules vs
                         setDecodedModules ds

                         addImportedThings isig ibuiltin hsImports)

              case r of
                  Left err               -> throwError err
                  Right (result, update) -> do
                    update
                    return (False, result)

readInterface :: FilePath -> TCM (Maybe Interface)
readInterface file = do
    -- Decode the interface file
    (s, close) <- liftIO $ readBinaryFile' file
    do  i <- liftIO . E.evaluate =<< decode s

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
    handler e = case errError e of
      IOException _ e -> do
        liftIO $ LocIO.putStrLn $ "IO exception: " ++ show e
        return Nothing   -- Work-around for file locking bug.
                         -- TODO: What does this refer to? Please
                         -- document.
      _               -> throwError e

-- | Writes the given interface to the given file. Returns the file's
-- new modification time stamp, or 'Nothing' if the write failed.

writeInterface :: FilePath -> Interface -> TCM ClockTime
writeInterface file i = do
    encodeFile file i
    liftIO $ getModificationTime file
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
  -> TCM (Interface, Either Warnings ClockTime)
createInterface file mname = do
    reportSLn "import.iface.create" 5  $
      "Creating interface for " ++ render (pretty mname) ++ "."
    verboseS "import.iface.create" 10 $ do
      visited <- Map.keys <$> getVisitedModules
      liftIO $ LocIO.putStrLn $
        "  visited: " ++ intercalate ", " (map (render . pretty) visited)

    previousHsImports <- getHaskellImports

    (pragmas, top) <- liftIO $ parseFile' moduleParser file

    pragmas <- concat <$> concreteToAbstract_ pragmas
               -- identity for top-level pragmas at the moment
    let getOptions (A.OptionsPragma opts) = Just opts
        getOptions _                      = Nothing
        options = catMaybes $ map getOptions pragmas
    mapM_ setOptionsFromPragma options
    topLevel <- concreteToAbstract_ (TopLevel top)

    termErrs <- catchError (do
      -- Type checking.
      checkDecls (topLevelDecls topLevel)

      -- Termination checking.
      termErrs <- ifM (optTerminationCheck <$> pragmaOptions)
                      (termDecls $ topLevelDecls topLevel)
                      (return [])
      mapM_ (\e -> reportSLn "term.warn.no" 2
                     (show (fst e) ++
                      " does NOT pass the termination checker."))
            termErrs
      return termErrs
      ) (\e -> do
        -- If there is an error syntax highlighting info can still be
        -- generated.
        case rStart $ getRange e of
          Just (Pn { srcFile = Just f }) | f == file -> do
            syntaxInfo <- generateSyntaxInfo file (Just e) topLevel []
            modFile    <- stModuleToSource <$> get
            -- The highlighting info is included with the error.
            case errHighlighting e of
              Just _  -> __IMPOSSIBLE__
              Nothing ->
                throwError $ e { errHighlighting =
                                   Just (syntaxInfo, modFile) }
          _ -> throwError e
      )

    -- Generate syntax highlighting info.
    syntaxInfo <- generateSyntaxInfo file Nothing topLevel termErrs

    -- Generate Vim file.
    whenM (optGenerateVimFile <$> commandLineOptions) $
	withScope_ (insideScope topLevel) $ generateVimFile $ filePath file

    -- Check if there are unsolved meta-variables...
    unsolvedOK    <- optAllowUnsolved <$> pragmaOptions
    unsolvedMetas <- List.nub <$> (mapM getMetaRange =<< getOpenMetas)
    unless (null unsolvedMetas || unsolvedOK) $
      typeError $ UnsolvedMetas unsolvedMetas

    -- ...or unsolved constraints
    unsolvedConstraints <- getConstraints
    unless (null unsolvedConstraints || unsolvedOK) $
      typeError $ UnsolvedConstraints unsolvedConstraints

    setScope $ outsideScope topLevel

    reportSLn "scope.top" 50 $ "SCOPE " ++ show (insideScope topLevel)

    i <- buildInterface topLevel syntaxInfo previousHsImports options

    if and [ null termErrs, null unsolvedMetas, null unsolvedConstraints ]
     then do
      -- The file was successfully type-checked (and no warnings were
      -- encountered), so the interface should be written out.
      t <- writeInterface (filePath $ toIFile file) i
      return (i, Right t)
     else
      return (i, Left $ Warnings termErrs unsolvedMetas unsolvedConstraints)

-- | Builds an interface for the current module, which should already
-- have been successfully type checked.

buildInterface :: TopLevelInfo
                  -- ^ 'TopLevelInfo' for the current module.
               -> HighlightingInfo
                  -- ^ Syntax highlighting info for the module.
               -> Set String
                  -- ^ Haskell modules imported in imported modules
                  -- (transitively).
               -> [OptionsPragma]
                  -- ^ Options set in @OPTIONS@ pragmas.
               -> TCM Interface
buildInterface topLevel syntaxInfo previousHsImports pragmas = do
    reportSLn "import.iface" 5 "Building interface..."
    scope'  <- getScope
    let scope = scope' { scopeCurrent = m }
    sig     <- getSignature
    builtin <- gets stLocalBuiltins
    ms      <- getImports
    hsImps  <- getHaskellImports
    let	builtin' = Map.mapWithKey (\x b -> fmap (const x) b) builtin
    reportSLn "import.iface" 7 "  instantiating all meta variables"
    i <- instantiateFull $ Interface
			{ iImportedModules = Set.toList ms
                        , iModuleName      = m
			, iScope	   = publicModules scope
                        , iInsideScope     = insideScope topLevel
			, iSignature	   = sig
			, iBuiltin	   = builtin'
                        , iHaskellImports  = Set.difference hsImps
                                                            previousHsImports
                        , iHighlighting    = syntaxInfo
                        , iPragmaOptions   = pragmas
			}
    reportSLn "import.iface" 7 "  interface complete"
    return i
  where m = topLevelModuleName topLevel

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
