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
import Agda.Utils.IO.Directory

import Agda.Compiler.UHC.CompileState
import Agda.Compiler.UHC.Bridge as UB
import Agda.Compiler.UHC.ModuleInfo
import qualified Agda.Compiler.UHC.FromAgda     as FAgda
--import qualified Agda.Compiler.UHC.Smashing     as Smash

#include "undefined.h"
import Agda.Utils.Impossible

-- we should use a proper build system to ensure that things get only built once,
-- but better than nothing
type CompModT = StateT CompModState

data CompModState = CompModState
  { compileInfo :: M.Map ModuleName (AModuleInfo)
  }

putCompModule :: Monad m => AModuleInfo -> CompModT m ()
putCompModule amod = modify (\s -> s
    { compileInfo = M.insert (amiModule amod) amod (compileInfo s) })

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


-- | Compile an interface into an executable using UHC
compilerMain
    :: [Interface] -- modules to compile. Imported modules will also be compiled,
                   -- no matter if they are mentioned here or not. The main module
                   -- should not be in this list.
    -> Maybe Interface -- The main module.
    -> TCM ()
compilerMain inters mainInter = do
    when (not uhcBackendEnabled) $ typeError $ GenericError "Agda has been built without UHC support. To use the UHC compiler you need to reinstall Agda with 'cabal install Agda -f uhc'."
    -- TODO we should do a version check here at some point.
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
                agdaPrimModInfo <- compileModule [] agdaPrimInter
                -- Always implicitly import Agda.Primitive now
                modInfos <- mapM (compileModule [agdaPrimInter]) inters
                let modInfos' = agdaPrimModInfo : modInfos

                case mainInter of
                  Nothing -> return (modInfos', Nothing)
                  Just mainInter' -> do
                    mainModInfo <- compileModule [agdaPrimInter] mainInter'
                    main <- lift $ getMain mainInter'
                    -- get core name from modInfo
                    crMain <- lift $ getCoreName1 main
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
    -> CompModT TCM AModuleInfo
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
            curModInfos <- mapM (compileModule addImps) imports

            -- check for uhc interface file
            lift $ reportSLn "" 1 $
              "Compiling: " ++ show (iModuleName i)
            opts <- lift commandLineOptions
            (code, modInfo) <- lift $ compileDefns modNm curModInfos opts i
            crFile <- lift $ getCorePath modInfo
            _ <- lift $ writeCoreFile crFile code

            putCompModule modInfo
            return modInfo


getCorePath :: AModuleInfo -> TCM FilePath
getCorePath amod = do
  let modParts = moduleNameToCoreNameParts (amiModule amod)
  outFile modParts
  where
    outFile :: [String] -> TCM FilePath
    outFile modParts = do
      let (dir, fn) = splitFileName $ foldl1 (</>) modParts
          fp  | dir == "./"  = fn
              | otherwise = dir </> fn
      liftIO $ createDirectoryIfMissing True dir
      return $ fp


getMain :: MonadTCM m => Interface -> m QName
getMain iface = case concatMap f defs of
    [] -> typeError $ GenericError $ "Could not find main."
    [x] -> return x
    _   -> __IMPOSSIBLE__
  where defs = HMap.toList $ sigDefinitions $ iSignature iface
        f (qn, def) = case theDef def of
            (Function{}) | "main" == show (qnameName qn) -> [qn]
            _   -> []

-- | Perform the chain of compilation stages, from definitions to UHC Core code
compileDefns :: ModuleName
    -> [AModuleInfo] -- ^ top level imports
    -> CommandLineOptions
    -> Interface -> TCM (UB.CModule, AModuleInfo)
compileDefns modNm curModImps opts iface = do

    (crMod, modInfo) <- FAgda.fromAgdaModule modNm curModImps iface

    reportSLn "uhc" 10 $ "Done generating Core for \"" ++ show modNm ++ "\"."
    return (crMod, modInfo)

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
                let mmod = FAgda.createMainModule mainMod mainName
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
