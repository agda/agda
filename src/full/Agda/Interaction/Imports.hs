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
import Agda.Interaction.Highlighting.Emacs
import Agda.Interaction.Highlighting.Vim
import qualified Agda.Interaction.Highlighting.Range as R

import Agda.Utils.FileName
import Agda.Utils.Monad
import Agda.Utils.IO

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
    visited <- Map.keys <$> getVisitedModules
    reportSLn "import.scope" 10 $ "  visited: " ++ show visited
    (i,t)   <- getInterface x
    addImport x
    return (iModuleName i `withRangesOfQ` mnameToConcrete x, iScope i)

alreadyVisited :: ModuleName -> TCM (Interface, ClockTime) -> TCM (Interface, ClockTime)
alreadyVisited x getIface = do
    mm <- getVisitedModule x
    case mm of
	Just it	-> do
            reportSLn "import.visit" 10 $ "  Already visited " ++ show x
            return it
	Nothing	-> do
	    reportSLn "import.visit" 5 $ "  Getting interface for " ++ show x
	    (i, t) <- getIface
	    reportSLn "import.visit" 5 $ "  Now we've looked at " ++ show x
	    visitModule x i t
	    return (i, t)

getInterface :: ModuleName -> TCM (Interface, ClockTime)
getInterface x = alreadyVisited x $ addImportCycleCheck x $ do
    file <- findFile SourceFile (toTopLevelModuleName x)
            -- requires source to exist

    reportSLn "import.iface" 10 $ "  Check for cycle"
    checkForImportCycle

    uptodate <- ifM ignoreInterfaces
		    (return False)
		    (liftIO $ toIFile file `isNewerThan` file)

    reportSLn "import.iface" 5 $ "  " ++ show x ++ " is " ++ (if uptodate then "" else "not ") ++ "up-to-date."

    (i,t) <- if uptodate
	then skip x file
	else typeCheck file

    visited <- isVisited x
    reportSLn "import.iface" 5 $ if visited then "  We've been here. Don't merge."
			         else "  New module. Let's check it out."
    unless visited $ mergeInterface i

    storeDecodedModule x i t
    return (i,t)

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
			    reportSLn "" 1 $ "Skipping " ++ show x ++ " (" ++ ifile ++ ")."
			    return (i, t)

	typeCheck file = do
	    -- Do the type checking
	    ms       <- getImportPath
	    vs       <- getVisitedModules
	    ds       <- getDecodedModules
	    opts     <- commandLineOptions
	    trace    <- getTrace
            isig     <- getImportedSignature
            ibuiltin <- gets stImportedBuiltins
	    r <- liftIO $ runTCM $ -- Every interface should be
	                           -- treated in isolation.
                   createInterface opts trace ms vs ds
                                   isig ibuiltin (Just x) file False

	    case r of
		Left err -> throwError err
                Right (_, Warnings termErrs@(_:_) []) -> do
                  typeError $ TerminationCheckFailed termErrs
                Right (_, Warnings _ _) -> __IMPOSSIBLE__
		Right (_, Success vs ds i isig ibuiltin)  -> do
                  -- writeInterface (used by createInterface) may
                  -- remove ifile.
                  let ifile = toIFile file
                  t <- liftIO $ ifM (doesFileExist ifile)
                         (getModificationTime ifile)
                         getClockTime
                  setVisitedModules vs
                  setDecodedModules ds
                  -- We need to add things imported when checking
                  -- the imported modules.
                  addImportedThings isig ibuiltin
                  return (i, t)

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

writeInterface :: FilePath -> Interface -> IO ()
writeInterface file i = do
    encodeFile file i
  `catch` \e -> do
    UTF8.putStrLn $ "failed to write interface " ++ file ++ " : " ++ show e
    removeFile file
    return ()

-- | Return type used by 'createInterface'.

data CreateInterfaceResult
  = Success { cirVisited   :: VisitedModules
            , cirDecoded   :: DecodedModules
            , cirInterface :: Interface
            , cirSignature :: Signature
            , cirBuiltin   :: BuiltinThings PrimFun
            }
    -- ^ Everything completed successfully, and an interface file was
    -- written.
  | Warnings { terminationProblems   :: [([QName], [R.Range])]
             , unsolvedMetaVariables :: [Range]
             }
    -- ^ Type checking was successful, except for some termination
    -- checking problems or unsolved meta-variables.
    --
    -- Meta-variable problems are reported as type errors unless we
    -- are type checking a top-level module and the flag to allow
    -- unsolved meta-variables has been selected.

-- | Tries to type check a module and write out its interface.
--
-- If appropriate this function writes out syntax highlighting
-- information.

createInterface
  :: CommandLineOptions
  -> CallTrace
  -> [ModuleName]
  -> VisitedModules
  -> DecodedModules
  -> Signature
  -> BuiltinThings PrimFun
  -> Maybe ModuleName       -- ^ Expected module name.
  -> FilePath               -- ^ The file to type check.
                            --   Must be an absolute path.
  -> Bool                   -- ^ Should relative include paths be
                            --   interpreted relative to the root
                            --   directory of the \"project\"
                            --   containing the file? (If not, then
                            --   they are interpreted relative to the
                            --   current working directory.)
  -> TCM (TopLevelInfo, CreateInterfaceResult)
createInterface opts trace path visited decoded
                isig ibuiltin mname file relativeToRoot
  | not (isAbsolute file) = __IMPOSSIBLE__
  | otherwise             = withImportPath path $ do
    setDecodedModules decoded
    setTrace trace
    setCommandLineOptions opts
    setVisitedModules visited

    reportSLn "" 1 $ "Checking " ++ (case mname of
                        Nothing -> file
                        Just m  -> show m ++ " (" ++ file ++ ")") ++ "."
    reportSLn "import.iface.create" 5  $ "Creating interface for " ++ show mname
    reportSLn "import.iface.create" 10 $ "  visited: " ++ show (Map.keys visited)

    addImportedThings isig ibuiltin

    pt@(pragmas, top) <- liftIO $ parseFile' moduleParser file
    let topLevelName = C.topLevelModuleName pt

    -- Make all the include directories absolute.
    if relativeToRoot then
      makeIncludeDirsAbsolute $ C.projectRoot file topLevelName
     else
      makeIncludeDirsAbsolute =<< liftIO getCurrentDirectory

    -- Make sure that the top-level module can be found under one of
    -- the include directories and is equal to the given file name.
    file' <- findFile' SourceFile topLevelName
    file' <- case file' of
               Left files  -> typeError $
                                ModuleNameDoesntMatchFileName topLevelName files
               Right file' -> return file'
    unless (file' == file) $
      typeError $ ModuleDefinedInOtherFile topLevelName file file'

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
        -- generated. Since there is no Vim highlighting for errors no
        -- Vim highlighting is generated, though.
        whenM (optGenerateEmacsFile <$> commandLineOptions) $ do
          writeEmacsFile =<<
            generateSyntaxInfo file TypeCheckingNotDone topLevel []

        throwError e)

    -- Generate syntax highlighting info.
    syntaxInfo <- generateSyntaxInfo file TypeCheckingDone
                                     topLevel termErrs

    -- Write Emacs file.
    whenM (optGenerateEmacsFile <$> commandLineOptions) $
      writeEmacsFile syntaxInfo

    -- Generate Vim file.
    whenM (optGenerateVimFile <$> commandLineOptions) $
	withScope_ (insideScope topLevel) $ generateVimFile file

    -- Check if there are unsolved meta-variables.
    unsolvedMetas <- List.nub <$> (mapM getMetaRange =<< getOpenMetas)
    case unsolvedMetas of
	[]  -> return ()
	_   -> do
          unsolvedOK <- optAllowUnsolved <$> commandLineOptions
          unless (unsolvedOK && path == []) $ do
            typeError $ UnsolvedMetas unsolvedMetas

    setScope $ outsideScope topLevel

    reportSLn "scope.top" 50 $ "SCOPE " ++ show (insideScope topLevel)

    -- True if the file was successfully and completely
    -- type-checked.
    let ok = null termErrs && null unsolvedMetas

    (,) topLevel <$> if ok then do
      i        <- buildInterface (topLevelModuleName topLevel) syntaxInfo
      isig     <- getImportedSignature
      vs       <- getVisitedModules
      ds       <- getDecodedModules
      ibuiltin <- gets stImportedBuiltins
      liftIO $ writeInterface (toIFile file) i
      modify (\s -> s { stCurrentModule =
                          Just (topLevelModuleName topLevel, i) })
      return (Success vs ds i isig ibuiltin)
     else
      return (Warnings termErrs unsolvedMetas)

-- | Builds an interface for the current module, which should already
-- have been successfully type checked.

buildInterface :: ModuleName
                  -- ^ The name of the current module.
               -> HighlightingInfo
                  -- ^ Syntax highlighting info for the module.
               -> TCM Interface
buildInterface m syntaxInfo = do
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
			, iSignature	   = sig
			, iBuiltin	   = builtin'
                        , iHaskellImports  = hsImps
                        , iHighlighting    = syntaxInfo
			}
    reportSLn "import.iface" 7 "  interface complete"
    return i

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
