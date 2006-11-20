{-# OPTIONS -fglasgow-exts #-}

{-| This modules deals with how to find imported modules and loading their
    interface files.
-}
module Interaction.Imports where

import Control.Monad.Error
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.List as List
import System.Directory
import System.Time

import qualified Syntax.Concrete.Name as C
import Syntax.Abstract.Name
import Syntax.Parser 
import Syntax.Scope
import Syntax.Translation.ConcreteToAbstract

import TypeChecking.Interface
import TypeChecking.Reduce
import TypeChecking.Monad
import TypeChecking.Monad.Builtin
import TypeChecking.Serialise
import TypeChecking.Primitive
import TypeChecker

import Interaction.Options
import Interaction.Vim.Highlight

import Utils.FileName
import Utils.Monad
import Utils.IO
import Utils.Serialise

-- | Merge an interface into the current proof state.
mergeInterface :: Interface -> TCM ()
mergeInterface i = do
    let sig	= iSignature i
	isig	= iImports i
	builtin = Map.toList $ iBuiltin i
	prim	= [ x | (_,Prim x) <- builtin ]
	bi	= Map.fromList [ (x,Builtin t) | (x,Builtin t) <- builtin ]
    modify $ \st -> st { stImportedModules = stImportedModules st ++ iImportedModules i
		       , stImports	   = Map.unions [stImports st, sig, isig]
		       , stBuiltinThings   = stBuiltinThings st `Map.union` bi
			    -- TODO: not safe (?) ^
		       }
    prim <- Map.fromList <$> mapM rebind prim
    modify $ \st -> st { stBuiltinThings = stBuiltinThings st `Map.union` prim
		       }
    where
	rebind x = do
	    pf <- rebindPrimitive x
	    return (x, Prim pf)

-- TODO: move
data FileType = SourceFile | InterfaceFile

findFile :: FileType -> ModuleName -> TCM FilePath
findFile ft m = do
    let x = mnameConcrete m
    dirs <- getIncludeDirs
    let files = [ dir ++ [slash] ++ file
		| dir  <- dirs
		, file <- map (moduleNameToFileName x) exts
		]
    files' <- liftIO $ filterM doesFileExist files
    case files' of
	[]	-> typeError $ FileNotFound m files
	[file]	-> return file
	_	-> typeError $ ClashingFileNamesFor m files'
    where
	exts = case ft of
		SourceFile    -> [".agda", ".lagda", ".agda2", ".lagda2", ".ag2"]
		InterfaceFile -> [".agdai", ".ai"]

scopeCheckImport :: ModuleName -> TCM ModuleScope
scopeCheckImport x = do
    i <- fst <$> getInterface x
    mergeInterface i
    addImport x
    return $ iScope i

getInterface :: ModuleName -> TCM (Interface, ClockTime)
getInterface x = addImportCycleCheck x $ do
    file   <- findFile SourceFile x	-- requires source to exist
    let ifile = setExtension ".agdai" file

    checkForImportCycle

    uptodate <- ifM ignoreInterfaces
		    (return False)
		    (liftIO $ ifile `isNewerThan` file)

    if uptodate
	then skip      ifile file
	else typeCheck ifile file

    where
	skip ifile file = do

	    -- Read interface file
	    (s, close)  <- liftIO $ readBinaryFile' ifile
	    let (i, ok) = deserialiseLazy s

	    -- Check that it's the right version
	    if iVersion i /= currentInterfaceVersion || not ok
		then do
		    -- We need to explicitly close the handle to make sure we
		    -- can write the new interface. We can't trust that the
		    -- garbage collect will close it for us in time.
		    liftIO close
		    typeCheck ifile file
		else do

		-- Check time stamp of imported modules
		t  <- liftIO $ getModificationTime ifile
		ts <- map snd <$> mapM getInterface (iImportedModules i)

		-- If any of the imports are newer we need to retype check
		if any (> t) ts
		    then do
			liftIO close	-- Close the interface file. See above.
			typeCheck ifile file
		    else do
			unlessM (isVisited x) $
			    reportLn 1 $ "Skipping " ++ show x ++ " ( " ++ ifile ++ " )"
			visitModule x
			return (i, t)

	typeCheck ifile file = do

	    -- Do the type checking
	    unlessM (isVisited x) $
		reportLn 1 $ "Checking " ++ show x ++ " ( " ++ file ++ " )"
	    visitModule x
	    ms	  <- getImportPath
	    vs	  <- getVisitedModules
	    opts  <- commandLineOptions
	    trace <- getTrace
	    r  <- liftIO $ createInterface opts trace ms vs file

	    -- Write interface file and return
	    case r of
		Left err -> throwError err
		Right (vs,i)  -> do
		    liftIO $ writeBinaryFile ifile (serialise i)
		    t <- liftIO $ getModificationTime ifile
		    setVisitedModules vs
		    return (i, t)

type Visited = [ModuleName]

createInterface :: CommandLineOptions -> CallTrace -> [ModuleName] -> Visited -> FilePath ->
		   IO (Either TCErr (Visited, Interface))
createInterface opts trace path visited file = runTCM $ withImportPath path $ do

    setTrace trace
    setCommandLineOptions opts
    setVisitedModules visited

    (pragmas, top) <- liftIO $ parseFile' moduleParser file
    pragmas	   <- concreteToAbstract_ pragmas -- identity for top-level pragmas
    (m, scope)	   <- concreteToAbstract_ (TopLevel top)

    setOptionsFromPragmas pragmas

    checkDecls m
    setScope scope

    -- Generate Vim file
    whenM (optGenerateVimFile <$> commandLineOptions) $
	generateVimFile file

    -- check that metas have been solved
    ms <- getOpenMetas
    case ms of
	[]  -> return ()
	_   -> do
	    rs <- mapM getMetaRange ms
	    typeError $ UnsolvedMetasInImport $ List.nub rs

    i  <- buildInterface
    vs <- getVisitedModules
    return (vs, i)

buildInterface :: TCM Interface
buildInterface = do
    scope   <- currentModuleScope <$> getScope
    sig	    <- getSignature
    isig    <- getImportedSignature
    builtin <- getBuiltinThings
    ms	    <- getImports
    let	builtin' = Map.mapWithKey (\x b -> fmap (const x) b) builtin
    instantiateFull $ Interface
			{ iVersion	   = currentInterfaceVersion
			, iImportedModules = ms
			, iScope	   = scope
			, iSignature	   = sig
			, iImports	   = isig
			, iBuiltin	   = builtin'
			}


-- | Put some of this stuff in a Utils.File
type Suffix = String

{-| Turn a module name into a file name with the given suffix.
-}
moduleNameToFileName :: C.QName -> Suffix -> FilePath
moduleNameToFileName (C.QName  x) ext = show x ++ ext
moduleNameToFileName (C.Qual m x) ext = show m ++ [slash] ++ moduleNameToFileName x ext

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


