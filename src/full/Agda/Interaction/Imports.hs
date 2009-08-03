{-# LANGUAGE CPP #-}
{-| This module deals with finding imported modules and loading their
    interface files.
-}
module Agda.Interaction.Imports where

import Prelude hiding (catch)

import Control.Monad.Error
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.ByteString.Lazy as BS
import Data.Generics
import Data.List
import Data.Map (Map)
import System.Directory
import System.Time
import Control.OldException
import qualified System.IO.UTF8 as UTF8
import System.FilePath hiding (splitPath)

import Agda.Syntax.Position
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

import Agda.Interaction.Options
import Agda.Interaction.Highlighting.Precise (HighlightingInfo)
import Agda.Interaction.Highlighting.Generate
import Agda.Interaction.Highlighting.Vim
import qualified Agda.Interaction.Highlighting.Range as R

import Agda.Utils.FileName
import Agda.Utils.Monad
import Agda.Utils.IO
import Agda.Utils.Pretty

import Agda.Utils.Impossible
#include "../undefined.h"

-- | Converts an Agda file name to the corresponding interface file
-- name.

toIFile :: FilePath -> FilePath
toIFile = setExtension ".agdai"

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
    modify $ \st -> st { stImports	    = unionSignatures [stImports st, sig]
		       , stImportedBuiltins = stImportedBuiltins st `Map.union` bi
		       }
    reportSLn "import.iface.merge" 20 $
      "  Rebinding primitives " ++ show prim
    prim <- Map.fromList <$> mapM rebind prim
    modify $ \st -> st { stImportedBuiltins = stImportedBuiltins st `Map.union` prim
		       }
    where
	rebind x = do
	    PrimImpl _ pf <- lookupPrimitiveFunction x
	    return (x, Prim pf)

addImportedThings :: Signature -> BuiltinThings PrimFun -> TCM ()
addImportedThings isig ibuiltin =
  modify $ \st -> st
    { stImports          = unionSignatures [stImports st, isig]
    , stImportedBuiltins = Map.union (stImportedBuiltins st) ibuiltin
    }

-- TODO: move
data FileType = SourceFile | InterfaceFile

-- | Finds the source or interface file corresponding to a given
-- top-level module name. The returned paths are absolute.
--
-- Raises an error if the file cannot be found.

findFile :: FileType -> C.TopLevelModuleName -> TCM FilePath
findFile ft m = do
  mf <- findFile' ft m
  case mf of
    Left files -> typeError $ FileNotFound m files
    Right f    -> return f

-- | Finds the source or interface file corresponding to a given
-- top-level module name. The returned paths are absolute.
--
-- Returns @'Left' files@ if the file cannot be found, where @files@
-- is the list of files which the module could have been defined in.

findFile' :: FileType -> C.TopLevelModuleName ->
             TCM (Either [FilePath] FilePath)
findFile' ft m = do
    dirs <- getIncludeDirs
    let files = [ dir ++ [slash] ++ file
		| dir  <- dirs
		, file <- map (C.moduleNameToFileName m) exts
		]
    files' <- liftIO $ filterM doesFileExist files
    files' <- liftIO $ nubFiles files'
    return $ case files' of
	[]	-> Left files
	file:_	-> Right file
    where
	exts = case ft of
		SourceFile    -> [".agda", ".lagda"]
		InterfaceFile -> [".agdai"]

-- | Scope checks the given module. A proper version of the module
-- name (with correct definition sites) is returned.

scopeCheckImport :: ModuleName -> TCM (ModuleName, Map ModuleName Scope)
scopeCheckImport x = do
    reportSLn "import.scope" 5 $ "Scope checking " ++ show x
    verboseS "import.scope" 10 $ do
      visited <- Map.keys <$> getVisitedModules
      liftIO $ UTF8.putStrLn $
        "  visited: " ++ intercalate ", " (map (render . pretty) visited)
    (i,t)   <- getInterface x
    addImport x
    return (iModuleName i `withRangesOfQ` mnameToConcrete x, iScope i)

-- | If the module has already been visited, then its interface is
-- returned directly. Otherwise the computation is used to find the
-- interface and the computed interface is stored for potential later
-- use.

alreadyVisited :: C.TopLevelModuleName ->
                  TCM (Interface, Either Warnings ClockTime) ->
                  TCM (Interface, Either Warnings ClockTime)
alreadyVisited x getIface = do
    mm <- getVisitedModule x
    case mm of
	Just (i, t) -> do
            reportSLn "import.visit" 10 $ "  Already visited " ++ render (pretty x)
            return (i, Right t)
	Nothing	-> do
	    reportSLn "import.visit" 5 $ "  Getting interface for " ++ render (pretty x)
	    r@(i, wt) <- getIface
	    reportSLn "import.visit" 5 $ "  Now we've looked at " ++ render (pretty x)
            case wt of
              Left w  -> visitModule i =<< liftIO getClockTime
              Right t -> visitModule i t
	    return r

-- | Which directory should form the base of relative include paths?

data RelativeTo
  = ProjectRoot
    -- ^ The root directory of the \"project\" containing the current
    -- file.
  | CurrentDir
    -- ^ The current working directory.

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
  }

-- | Turns warnings into an error. Even if several errors are possible
-- only one is raised.

warningsToError :: Warnings -> TypeError
warningsToError (Warnings [] [])     = __IMPOSSIBLE__
warningsToError (Warnings _ w@(_:_)) = UnsolvedMetas w
warningsToError (Warnings w@(_:_) _) = TerminationCheckFailed w

-- | Type checks the given file (if necessary), after making relative
-- include directories absolute.

-- Note that the given file may be parsed twice: once to find the
-- module name, and once again if the module needs to be type checked.

typeCheck :: FilePath
          -- ^ The file name is interpreted relative to the current
          -- working directory (unless it is absolute).
          -> RelativeTo
          -> TCM (Interface, Either Warnings ClockTime)
typeCheck file relativeTo = do
  -- canonicalizePath seems to return absolute paths.
  file <- liftIO $ canonicalizePath file

  topLevelName <- moduleName file relativeTo

  getInterface' topLevelName True

-- | Computes the module name of the top-level module in the given
-- file. An error is raised if the file name does not match the module
-- name.
--
-- The function also makes relative include directories absolute.

moduleName :: FilePath
           -- ^ The file name is interpreted relative to the current
           -- working directory (unless it is absolute).
           -> RelativeTo
           -> TCM C.TopLevelModuleName
moduleName file relativeTo = do
  m <- C.topLevelModuleName <$> liftIO (parseFile' moduleParser file)

  -- Make all the include directories absolute.
  makeIncludeDirsAbsolute =<< case relativeTo of
    CurrentDir  -> liftIO getCurrentDirectory
    ProjectRoot -> return $ C.projectRoot file m

  checkModuleName m file

  return m

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
  alreadyVisited x $ addImportCycleCheck x $ do
    file <- findFile SourceFile x  -- requires source to exist

    reportSLn "import.iface" 10 $ "  Check for cycle"
    checkForImportCycle

    uptodate <- ifM ignoreInterfaces
		    (return False)
		    (liftIO $ toIFile file `isNewerThan` file)

    reportSLn "import.iface" 5 $
      "  " ++ render (pretty x) ++ " is " ++
      (if uptodate then "" else "not ") ++ "up-to-date."

    r@(i, wt) <- if uptodate
	         then skip x file
	         else typeCheck file

    visited <- isVisited x
    reportSLn "import.iface" 5 $ if visited then "  We've been here. Don't merge."
                                 else "  New module. Let's check it out."
    unless (visited || includeStateChanges) $ mergeInterface i

    modify (\s -> s { stCurrentModule = Just $ iModuleName i })

    case wt of
      Left  w -> storeDecodedModule i =<< liftIO getClockTime
      Right t -> storeDecodedModule i t

    return r

    where
	skip x file = do
	    -- Examine the mtime of the interface file. If it is newer than the
	    -- stored version (in stDecodedModules), or if there is no stored version,
	    -- read and decode it. Otherwise use the stored version.
            let ifile = toIFile file
	    t  <- liftIO $ getModificationTime ifile
	    mm <- getDecodedModule x
	    mi <- case mm of
		      Just (im, tm) ->
			 if tm < t
			 then do dropDecodedModule x
				 reportSLn "import.iface" 5 $ "  file is newer, re-reading " ++ ifile
				 liftIO $ readInterface ifile
			 else do reportSLn "import.iface" 5 $ "  using stored version of " ++ ifile
				 return (Just im)
		      Nothing ->
			 do reportSLn "import.iface" 5 $ "  no stored version, reading " ++ ifile
			    liftIO $ readInterface ifile

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
			    reportSLn "" 1 $ "Skipping " ++ render (pretty x) ++ " (" ++ ifile ++ ")."
			    return (i, Right t)

	typeCheck file = do
	    -- Do the type checking.
            reportSLn "" 1 $ "Checking " ++ render (pretty x) ++ " (" ++ file ++ ")."
            if includeStateChanges then
              createInterface file x
             else do
              ms       <- getImportPath
              vs       <- getVisitedModules
              ds       <- getDecodedModules
              opts     <- commandLineOptions
              trace    <- getTrace
              isig     <- getImportedSignature
              ibuiltin <- gets stImportedBuiltins
              -- Every interface is treated in isolation.
              r <- liftIO $ runTCM $
                     withImportPath ms $ do
                       setDecodedModules ds
                       setTrace trace
                       setCommandLineOptions opts
                       setVisitedModules vs
                       addImportedThings isig ibuiltin

                       r <- createInterface file x

                       vs       <- getVisitedModules
                       ds       <- getDecodedModules
                       isig     <- getImportedSignature
                       ibuiltin <- gets stImportedBuiltins
                       return $ (r, do
                         setVisitedModules vs
                         setDecodedModules ds
                         addImportedThings isig ibuiltin)

              case r of
                  Left err               -> throwError err
                  Right (result, update) -> do
                    update
                    return result

readInterface :: FilePath -> IO (Maybe Interface)
readInterface file = do
    -- Decode the interface file
    (s, close) <- readBinaryFile' file
    do  i <- decode s

        -- Force the entire string, to allow the file to be closed.
        let n = BS.length s
        () <- when (n == n) $ return ()

        -- Close the file
        close

	-- Force the interface to make sure the interface version is looked at
        i `seq` return $ Just i
      -- Catch exceptions and close
      `catch` \e -> close >> handler e
  -- Catch exceptions
  `catch` handler
  where
    handler e = case e of
      ErrorCall _   -> return Nothing
      IOException e -> do
          UTF8.putStrLn $ "IO exception: " ++ show e
          return Nothing   -- work-around for file locking bug
      _		    -> throwIO e

-- | Writes the given interface to the given file. Returns the file's
-- new modification time stamp, or 'Nothing' if the write failed.

writeInterface :: FilePath -> Interface -> TCM ClockTime
writeInterface file i =
  liftIO (do
    encodeFile file i
    getModificationTime file)
  `catchError` \e -> do
    reportSLn "" 1 $
      "Failed to write interface " ++ file ++ "."
    liftIO $ removeFile file
    throwError e

-- | Tries to type check a module and write out its interface. The
-- function only writes out an interface file if it does not encounter
-- any warnings.
--
-- If appropriate this function writes out syntax highlighting
-- information.

createInterface
  :: FilePath              -- ^ The file to type check. Must be an absolute path.
  -> C.TopLevelModuleName  -- ^ The expected module name.
  -> TCM (Interface, Either Warnings ClockTime)
createInterface file mname
  | not (isAbsolute file) = __IMPOSSIBLE__
  | otherwise             = do
    reportSLn "import.iface.create" 5  $
      "Creating interface for " ++ render (pretty mname) ++ "."
    verboseS "import.iface.create" 10 $ do
      visited <- Map.keys <$> getVisitedModules
      liftIO $ UTF8.putStrLn $
        "  visited: " ++ intercalate ", " (map (render . pretty) visited)

    m@(pragmas, top) <- liftIO $ parseFile' moduleParser file
    let topLevelName = C.topLevelModuleName m

    -- Make sure that the given module name matches the one in the
    -- file.
    unless (topLevelName == mname) $ do
      checkModuleName topLevelName file
      __IMPOSSIBLE__

    pragmas <- concat <$> concreteToAbstract_ pragmas
               -- identity for top-level pragmas at the moment
    -- Note that pragmas can affect scope checking.
    setOptionsFromPragmas pragmas
    topLevel <- concreteToAbstract_ (TopLevel top)

    termErrs <- catchError (do
      -- Type checking.
      checkDecls (topLevelDecls topLevel)

      -- Termination checking.
      termErrs <- ifM (optTerminationCheck <$> commandLineOptions)
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
          Just (Pn { srcFile = f }) | f == file -> do
            syntaxInfo <- generateSyntaxInfo file (Just e) topLevel []
            -- The highlighting info is included with the error.
            case errHighlighting e of
              Just _  -> __IMPOSSIBLE__
              Nothing ->
                throwError $ e { errHighlighting = Just syntaxInfo }
          _ -> throwError e
      )

    -- Generate syntax highlighting info.
    syntaxInfo <- generateSyntaxInfo file Nothing topLevel termErrs

    -- Generate Vim file.
    whenM (optGenerateVimFile <$> commandLineOptions) $
	withScope_ (insideScope topLevel) $ generateVimFile file

    -- Check if there are unsolved meta-variables.
    unsolvedMetas <- List.nub <$> (mapM getMetaRange =<< getOpenMetas)
    case unsolvedMetas of
	[]  -> return ()
	_   -> do
          unsolvedOK <- optAllowUnsolved <$> commandLineOptions
          unless unsolvedOK $
            typeError $ UnsolvedMetas unsolvedMetas

    setScope $ outsideScope topLevel

    reportSLn "scope.top" 50 $ "SCOPE " ++ show (insideScope topLevel)

    i <- buildInterface topLevel syntaxInfo

    if null termErrs && null unsolvedMetas then do
      -- The file was successfully and completely type-checked, so the
      -- interface should be written out.
      t <- writeInterface (toIFile file) i
      return (i, Right t)
     else
      return (i, Left $ Warnings termErrs unsolvedMetas)

-- | Builds an interface for the current module, which should already
-- have been successfully type checked.

buildInterface :: TopLevelInfo
                  -- ^ 'TopLevelInfo' for the current module.
               -> HighlightingInfo
                  -- ^ Syntax highlighting info for the module.
               -> TCM Interface
buildInterface topLevel syntaxInfo = do
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
                        , iHaskellImports  = hsImps
                        , iHighlighting    = syntaxInfo
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

-- | Ensures that the module name matches the file name. The file
-- corresponding to the module name (according to the include path)
-- has to be the same as the given file name.

checkModuleName :: C.TopLevelModuleName
                   -- ^ The name of the module.
                -> FilePath
                   -- ^ The file from which it was loaded.
                -> TCM ()
checkModuleName name file = do
  moduleShouldBeIn <- findFile' SourceFile name
  case moduleShouldBeIn of
    Left files  -> typeError $
                     ModuleNameDoesntMatchFileName name files
    Right file' -> if file' == file then
                     return ()
                    else
                     typeError $
                       ModuleDefinedInOtherFile name file file'
