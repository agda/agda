{-# LANGUAGE CPP             #-}
{-# LANGUAGE DoAndIfThenElse #-}

-- | UHC compiler backend, main entry point.

-- In the long term, it would be nice if we could use e.g. shake to build individual Agda modules. The problem with that is that
-- some parts need to be in the TCM Monad, which doesn't easily work in shake. We would need a way to extract the information
-- out of the TCM monad, so that we can pass it to the compilation function without pulling in the TCM Monad. Another minor
-- problem might be error reporting?
module Agda.Compiler.UHC.Compiler(compilerMain) where

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative
import Data.Monoid
#endif

import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.ByteString.Lazy as BS
import qualified Data.Map as M
import Data.Maybe

import System.Directory ( canonicalizePath, createDirectoryIfMissing
                        , setCurrentDirectory
                        , doesDirectoryExist
                        , getDirectoryContents, copyFile
                        )
import Data.List as L
import System.Exit
import System.FilePath hiding (normalise)

import Paths_Agda
import Agda.Compiler.CallCompiler
import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Interaction.Imports
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Syntax.Internal hiding (Term(..))
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Serialise
import Agda.Utils.FileName
import Agda.Utils.Pretty
import qualified Agda.Utils.HashMap as HMap

import Agda.Compiler.UHC.Bridge as UB
import Agda.Compiler.UHC.Transform
import Agda.Compiler.UHC.ModuleInfo
import Agda.Compiler.UHC.Core
import qualified Agda.Compiler.UHC.FromAgda     as FAgda
import qualified Agda.Compiler.UHC.Smashing     as Smash
import Agda.Compiler.UHC.Naming
import Agda.Compiler.UHC.AuxAST

#include "undefined.h"
import Agda.Utils.Impossible

-- we should use a proper build system to ensure that things get only built once,
-- but better than nothing
type CompModT = StateT CompModState

data CompModState = CompModState
  { compileInfo :: M.Map ModuleName (AModuleInfo, AModuleInterface)
  }

putCompModule :: Monad m => AModuleInfo -> AModuleInterface -> CompModT m ()
putCompModule amod modTrans = modify (\s -> s
    { compileInfo = M.insert (amiModule amod) (amod, modTrans) (compileInfo s) })

emptyCompModState :: CompModState
emptyCompModState = CompModState M.empty

-- for the time being, we just copy the base library into the generated code.
-- We don't install it into the user db anymore, as that gets complicated when
-- multiple Agda instances run concurrently.
-- Just copying it is safe for the time being, as we only have full-program
-- compilation at the moment.
copyUHCAgdaBase :: FilePath -> TCM ()
copyUHCAgdaBase outDir = do
    dataDir <- liftIO getDataDir
    let srcDir = dataDir </> "uhc-agda-base" </> "src" </> "UHC"

    liftIO $ copyDirContent srcDir (outDir </> "UHC")

  where copyDirContent :: FilePath -> FilePath -> IO ()
        copyDirContent src dest = do
            createDirectoryIfMissing True dest
            chlds <- getDirectoryContents src
            mapM_ (\x -> do
                isDir <- doesDirectoryExist (src </> x)
                case isDir of
                    _ | x == "." || x == ".." -> return ()
                    True  -> copyDirContent (src </> x) (dest </> x)
                    False -> copyFile (src </> x) (dest </> x)
              ) chlds

-- | Compile an interface into an executable using UHC
compilerMain
    :: [Interface] -- modules to compile. Imported modules will also be compiled,
                   -- no matter if they are mentioned here or not. The main module
                   -- should not be in this list.
    -> Maybe Interface -- The main module.
    -> TCM ()
compilerMain inters mainInter = do
    when (not uhcBackendEnabled) $ typeError $ GenericError "Agda has been built without UHC support. To use the UHC compiler you need to reinstall Agda with 'cabal install Agda -f uhc'."
    -- TODO do proper check for uhc existance
    let uhc_exist = ExitSuccess
    case uhc_exist of
        ExitSuccess -> do
            outDir <- setUHCDir (fromMaybe (head inters) mainInter)

            -- look for the Agda.Primitive interface in visited modules.
            -- (It will not be in ImportedModules, if it has not been
            -- explicitly imported)
            -- TODO this should be done in a more clean way
            [agdaPrimInter] <- filter (("Agda.Primitive"==) . prettyShow . iModuleName) . map (miInterface) . M.elems
                <$> getVisitedModules


            copyUHCAgdaBase outDir
            (modInfos, mainInfo) <- evalStateT (do
                -- first compile the Agda.Primitive module
                agdaPrimModInfo <- fst <$> compileModule [] agdaPrimInter
                -- Always implicitly import Agda.Primitive now
                modInfos <- fst . unzip <$> mapM (compileModule [agdaPrimInter]) inters
                let modInfos' = agdaPrimModInfo : modInfos

                case mainInter of
                  Nothing -> return (modInfos', Nothing)
                  Just mainInter' -> do
                    mainModInfo <- fst <$> compileModule [agdaPrimInter] mainInter'
                    main <- lift $ getMain mainInter'
                    -- get core name from modInfo
                    let crMain = cnName $ fromJust $ qnameToCoreName (amifNameMp $ amiInterface mainModInfo) main
                    return (modInfos', Just (mainModInfo, crMain))
                )
                emptyCompModState

            runUhcMain modInfos mainInfo
            return ()

        ExitFailure _ -> internalError $ unlines
           [ "Agda cannot find the UHC compiler."
           ]

auiFile :: CN.TopLevelModuleName -> TCM FilePath
auiFile modNm = do
  let (dir, fn) = splitFileName . foldl1 (</>) $ ("Cache" : (CN.moduleNameParts modNm))
      fp  | dir == "./"  = fn
          | otherwise = dir </> fn
  liftIO $ createDirectoryIfMissing True dir
  return $ fp


-- | Compiles a module and it's imports. Returns the module info
-- of this module, and the accumulating module interface.
compileModule :: [Interface] -- additional modules to import. Used to bring Agda.Primitive in scope.
    -> Interface
    -> CompModT TCM (AModuleInfo, AModuleInterface)
compileModule addImps i = do
    -- we can't use the Core module name to get the name of the aui file,
    -- as we don't know the Core module name before we loaded/compiled the file.
    -- (well, we could just compute the module name and use that, that's
    -- probably better? )
    compMods <- gets compileInfo
    let modNm = iModuleName i
    let topModuleName = toTopLevelModuleName modNm
    auiFile' <- lift $ auiFile topModuleName
    -- check if this module has already been compiled
    case M.lookup modNm compMods of
        Just x -> return x
        Nothing  -> do
            imports <- (addImps ++) . map miInterface . catMaybes
                                      <$> lift (mapM (getVisitedModule . toTopLevelModuleName . fst)
                                                     (iImportedModules i))
            (curModInfos, transModInfos) <- (fmap mconcat) . unzip <$> mapM (compileModule addImps) imports
            ifile <- maybe __IMPOSSIBLE__ filePath <$> lift (findInterfaceFile topModuleName)
            let uifFile = auiFile' <.> "aui"
            uptodate <- liftIO $ isNewerThan uifFile ifile
            lift $ reportSLn "UHC" 15 $ "Interface file " ++ uifFile ++ " is uptodate: " ++ show uptodate
            -- check for uhc interface file
            modInfoCached <- case uptodate of
              True  -> do
                    lift $ reportSLn "" 5 $
                        show modNm ++ " : UHC backend interface file is up to date."
                    uif <- lift $ readModInfoFile uifFile
                    case uif of
                      Nothing -> do
                        lift $ reportSLn "" 5 $
                            show modNm ++ " : Could not read UHC interface file, will compile this module from scratch."
                        return Nothing
                      Just uif' -> do
                        -- now check if the versions inside modInfos match with the dep info
                        let deps = amiDepsVersion uif'
                        if depsMatch deps curModInfos then do
                          lift $ reportSLn "" 1 $
                            show modNm ++ " : module didn't change, skip compiling it."
                          return $ Just uif'
                        else
                          return Nothing
              False -> return Nothing

            case modInfoCached of
              Just x  -> let tmi' = transModInfos `mappend` (amiInterface x) in putCompModule x tmi' >> return (x, tmi')
              Nothing -> do
                    lift $ reportSLn "" 1 $
                        "Compiling: " ++ show (iModuleName i)
                    opts <- lift commandLineOptions
                    (code, modInfo, _) <- lift $ compileDefns modNm curModInfos transModInfos opts i
                    lift $ do
                        crFile <- getCorePath modInfo
                        _ <- writeCoreFile crFile code
                        writeModInfoFile uifFile modInfo

                    let tmi' = transModInfos `mappend` amiInterface modInfo
                    putCompModule modInfo tmi'
                    return (modInfo, tmi')

  where depsMatch :: [(ModuleName, ModVersion)] -> [AModuleInfo] -> Bool
        depsMatch modDeps otherMods = all (checkDep otherMods) modDeps
        checkDep :: [AModuleInfo] -> (ModuleName, ModVersion) -> Bool
        checkDep otherMods (nm, v) = case find ((nm==) . amiModule) otherMods of
                    Just v' -> (amiVersion v') == v
                    Nothing -> False

getCorePath :: AModuleInfo -> TCM FilePath
getCorePath amod = do
  let modParts = fst $ fromMaybe __IMPOSSIBLE__ $ mnameToCoreName (amifNameMp $ amiInterface amod) (amiModule amod)
  outFile modParts
  where
    outFile :: [String] -> TCM FilePath
    outFile modParts = do
      let (dir, fn) = splitFileName $ foldl1 (</>) modParts
          fp  | dir == "./"  = fn
              | otherwise = dir </> fn
      liftIO $ createDirectoryIfMissing True dir
      return $ fp


readModInfoFile :: String -> TCM (Maybe AModuleInfo)
readModInfoFile f = do
  modInfo <- liftIO (BS.readFile f) >>= decode
  return $ maybe Nothing (\mi ->
    if amiFileVersion mi == currentModInfoVersion then
      Just mi
    else
      Nothing) modInfo

writeModInfoFile :: String -> AModuleInfo -> TCM ()
writeModInfoFile f mi = do
  mi' <- encode mi
  liftIO $ BS.writeFile f mi'

getMain :: MonadTCM m => Interface -> m QName
getMain iface = case concatMap f defs of
    [] -> typeError $ GenericError $ "Could not find main."
    [x] -> return x
    _   -> __IMPOSSIBLE__
  where defs = HMap.toList $ sigDefinitions $ iSignature iface
        f (qn, def) = case theDef def of
            (Function{}) | "main" == show (qnameName qn) -> [qn]
            _   -> []

idPrint :: String -> Transform -> Transform
idPrint s m x = do
  reportSLn "uhc.phases" 10 s
  m x

-- | Perform the chain of compilation stages, from definitions to UHC Core code
compileDefns :: ModuleName
    -> [AModuleInfo] -- ^ top level imports
    -> AModuleInterface -- ^ transitive iface
    -> CommandLineOptions
    -> Interface -> TCM (UB.CModule, AModuleInfo, AMod)
compileDefns modNm curModImps transModIface opts iface = do

    (amod', modInfo) <- FAgda.fromAgdaModule modNm curModImps transModIface iface $ \amod ->
                   return amod
               >>= optim optOptimSmashing "smashing"      Smash.smash'em
               >>= idPrint "done" return
    reportSLn "uhc" 10 $ "Done generating AuxAST for \"" ++ show modNm ++ "\"."
    crMod <- toCore amod' modInfo (transModIface `mappend` (amiInterface modInfo)) curModImps

    reportSLn "uhc" 10 $ "Done generating Core for \"" ++ show modNm ++ "\"."
    return (crMod, modInfo, amod')
  where optim :: (CommandLineOptions -> Bool) -> String -> Transform -> Transform
        optim p s m x | p opts = idPrint s m x
                      | otherwise = return x

writeCoreFile :: String -> UB.CModule -> TCM FilePath
writeCoreFile f cmod = do
  useTextual <- optUHCTextualCore <$> commandLineOptions

  -- dump textual core, useful for debugging.
  when useTextual (do
    let f' = f <.> ".dbg.tcr"
    reportSLn "uhc" 10 $ "Writing textual core to \"" ++ show f' ++ "\"."
    liftIO $ putPPFile f' (UB.printModule defaultEHCOpts cmod) 200
    )

  let f' = f <.> ".bcr"
  reportSLn "uhc" 10 $ "Writing binary core to \"" ++ show f' ++ "\"."
  liftIO $ putSerializeFile f' cmod
  return f'

-- | Change the current directory to UHC folder, create it if it doesn't already
--   exist.
setUHCDir :: Interface -> TCM FilePath
setUHCDir mainI = do
    let tm = toTopLevelModuleName $ iModuleName mainI
    f <- findFile tm
    compileDir' <- gets (fromMaybe (filePath $ CN.projectRoot f tm) .
                                  optCompileDir . stPersistentOptions . stPersistentState)
    compileDir <- liftIO $ canonicalizePath compileDir'
    liftIO $ setCurrentDirectory compileDir
    liftIO $ createDirectoryIfMissing False "UHC"
    liftIO $ setCurrentDirectory $ compileDir </> "UHC"
    return $ compileDir </> "UHC"

-- | Create the UHC Core main file, which calls the Agda main function
runUhcMain
    :: [AModuleInfo]    -- other modules to compile
    -> Maybe (AModuleInfo, HsName)  -- main module
    -> TCM ()
runUhcMain otherMods mainInfo = do
    otherFps <- mapM getCorePath otherMods
    allFps <- (otherFps++)
        <$> case mainInfo of
            Nothing -> return []
            Just (mainMod, mainName) -> do
                let fp = "Main"
                let mmod = createMainModule mainMod mainName
                fp' <- writeCoreFile fp mmod
                return [fp']

    let extraOpts = maybe
            ["--compile-only"]
            ((\x -> [x]) . ("--output="++) . prettyShow . last . mnameToList . amiModule . fst)
            mainInfo

    -- TODO drop the RTS args as soon as we don't need the additional memory anymore
    callUHC1 $  ["--pkg-hide-all", "--pkg-expose=uhcbase", "--pkg-expose=base"
                ] ++ extraOpts ++ allFps ++ ["+RTS", "-K50m", "-RTS"]

callUHC1 :: [String] -> TCM ()
callUHC1 args = do
    uhcBin <- getUhcBin
    doCall <- optUHCCallUHC <$> commandLineOptions
    if doCall
    then callCompiler uhcBin args
    else reportSLn "" 1 $ "NOT Calling: " ++ intercalate " " (uhcBin : args)

getUhcBin :: TCM FilePath
getUhcBin = fromMaybe ("uhc") . optUHCBin <$> commandLineOptions
