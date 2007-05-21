{-# OPTIONS -fglasgow-exts #-}

{-| This modules deals with how to find imported modules and loading their
    interface files.
-}
module Interaction.Imports where

import Prelude hiding (putStrLn, putStr, print, catch)

import Control.Monad.Error
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Set as Set
import Data.Generics
import System.Directory
import System.Time
import Control.Exception

import qualified Syntax.Concrete.Name as C
import Syntax.Abstract.Name
import Syntax.Parser 
import Syntax.Scope.Base
import Syntax.Translation.ConcreteToAbstract

import TypeChecking.Reduce
import TypeChecking.Monad
import TypeChecking.Monad.Builtin
import TypeChecking.Serialise
import TypeChecking.Primitive
import TypeChecker

import Interaction.Options
import Interaction.Highlighting.Vim

import Utils.FileName
import Utils.Monad
import Utils.IO
-- import Utils.Serialise

-- | Merge an interface into the current proof state.
mergeInterface :: Interface -> TCM ()
mergeInterface i = do
    let sig	= iSignature i
	isig	= iImports i
	builtin = Map.toList $ iBuiltin i
	prim	= [ x | (_,Prim x) <- builtin ]
	bi	= Map.fromList [ (x,Builtin t) | (x,Builtin t) <- builtin ]
    modify $ \st -> st { stImportedModules = Set.union
						(stImportedModules st)
						(Set.fromList $ iImportedModules i)
		       , stImports	   = unionSignatures [stImports st, sig, isig]
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
    let x = mnameToConcrete m
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

scopeCheckImport :: ModuleName -> TCM Scope
scopeCheckImport x = do
    reportLn 5 $ "Scope checking " ++ show x
    visited <- Map.keys <$> getVisitedModules
    reportLn 10 $ "  visited: " ++ show visited
    visited <- isVisited x
    reportLn 5 $ if visited then "  We've been here. Don't merge."
			    else "  New module. Let's check it out."
    (i,t)   <- getInterface x
    unless visited $ mergeInterface i
    addImport x
    return $ iScope i

alreadyVisited :: ModuleName -> TCM (Interface, ClockTime) -> TCM (Interface, ClockTime)
alreadyVisited x getIface = do
    mm <- getVisitedModule x
    case mm of
	Just it	-> return it
	Nothing	-> do
	    reportLn 5 $ "  Getting interface for " ++ show x
	    (i, t) <- getIface
	    reportLn 5 $ "  Now we've looked at " ++ show x
	    visitModule x i t
	    return (i, t)

getInterface :: ModuleName -> TCM (Interface, ClockTime)
getInterface x = alreadyVisited x $ addImportCycleCheck x $ do
    file   <- findFile SourceFile x	-- requires source to exist
    let ifile = setExtension ".agdai" file

    reportLn 5 $ "  Check for cycle"
    checkForImportCycle

    uptodate <- ifM ignoreInterfaces
		    (return False)
		    (liftIO $ ifile `isNewerThan` file)

    reportLn 5 $ "  " ++ show x ++ " is " ++ (if uptodate then "" else "not ") ++ "up-to-date."

    if uptodate
	then skip      ifile file
	else typeCheck ifile file

    where
	skip ifile file = do

	    reportLn 5 $ "  reading interface file " ++ ifile

	    -- Read interface file
	    mi <- liftIO $ readInterface ifile

	    -- Check that it's the right version
	    case mi of
		Nothing	-> do
		    reportLn 5 $ "  bad interface, re-type checking"
		    typeCheck ifile file
		Just i	-> do

		    -- Check time stamp of imported modules
		    t  <- liftIO $ getModificationTime ifile

		    reportLn 5 $ "  imports: " ++ show (iImportedModules i)

		    ts <- map snd <$> mapM getInterface (iImportedModules i)

		    -- If any of the imports are newer we need to retype check
		    if any (> t) ts
			then do
			    -- liftIO close	-- Close the interface file. See above.
			    typeCheck ifile file
			else do
			    reportLn 1 $ "Skipping " ++ show x ++ " ( " ++ ifile ++ " )"
			    return (i, t)

	typeCheck ifile file = do

	    -- Do the type checking
	    reportLn 1 $ "Checking " ++ show x ++ " ( " ++ file ++ " )"
	    ms	  <- getImportPath
	    vs	  <- getVisitedModules
	    opts  <- commandLineOptions
	    trace <- getTrace
	    r  <- liftIO $ createInterface opts trace ms vs file

	    -- Write interface file and return
	    case r of
		Left err -> throwError err
		Right (vs,i)  -> do
		    -- liftIO $ writeBinaryFile ifile (serialise i)
		    liftIO $ writeInterface ifile i
		    t <- liftIO $ getModificationTime ifile
		    setVisitedModules vs
		    return (i, t)

readInterface :: FilePath -> IO (Maybe Interface)
readInterface file = do

    -- Decode the interface file
    (s, close) <- readBinaryFile' file
    let i = decode s

    -- Force the entire interface, to allow the file to be closed.
    let add x y = ((+) $! x) $! y
    () <- when (0 == everything add (const 1) i) $ return ()

    -- Close the file
    close

    return $ Just i

  -- Catch exceptions
  `catch` \e -> do
	case e of
	    ErrorCall _   -> return Nothing
	    IOException e -> do
		putStrLn $ "IO exception: " ++ show e
		return Nothing   -- work-around for file locking bug
	    _		  -> throwIO e

writeInterface :: FilePath -> Interface -> IO ()
writeInterface file i = do
    encodeFile file i
  `catch` \e -> do
    putStrLn $ "failed to write interface: " ++ show e
    return ()

createInterface :: CommandLineOptions -> CallTrace -> [ModuleName] -> VisitedModules -> FilePath ->
		   IO (Either TCErr (VisitedModules, Interface))
createInterface opts trace path visited file = runTCM $ withImportPath path $ do

    setTrace trace
    setCommandLineOptions opts
    setVisitedModules visited
    mapM_ (mergeInterface . fst) $ Map.elems visited

    (pragmas, top) <- liftIO $ parseFile' moduleParser file
    pragmas	   <- concreteToAbstract_ pragmas -- identity for top-level pragmas
    topLevel	   <- concreteToAbstract_ (TopLevel top)

    setOptionsFromPragmas pragmas

    checkDecls $ topLevelDecls topLevel

    -- Generate Vim file
    whenM (optGenerateVimFile <$> commandLineOptions) $
	withScope_ (insideScope topLevel) $ generateVimFile file

    -- check that metas have been solved
    ms <- getOpenMetas
    case ms of
	[]  -> return ()
	_   -> do
	    rs <- mapM getMetaRange ms
	    typeError $ UnsolvedMetasInImport $ List.nub rs

    setScope $ outsideScope topLevel

    i  <- buildInterface
    vs <- getVisitedModules
    return (vs, i)

buildInterface :: TCM Interface
buildInterface = do
    reportLn 5 "Building interface..."
    scope   <- getScope
    sig	    <- getSignature
    isig    <- getImportedSignature
    builtin <- getBuiltinThings
    ms	    <- getImports
    let	builtin' = Map.mapWithKey (\x b -> fmap (const x) b) builtin
    reportLn 7 "  instantiating all meta variables"
    i <- instantiateFull $ Interface
			{ iVersion	   = currentInterfaceVersion
			, iImportedModules = Set.toList ms
			, iScope	   = head $ scopeStack scope -- TODO!!
			, iSignature	   = sig
			, iImports	   = isig
			, iBuiltin	   = builtin'
			}
    reportLn 7 "  interface complete"
    return i


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


