{-# LANGUAGE CPP, DoAndIfThenElse #-}
-- | UHC compiler backend.

-- In the long term, it would be nice if we could use e.g. shake to build individual Agda modules. The problem with that is that
-- some parts need to be in the TCM Monad, which doesn't easily work in shake. We would need a way to extract the information
-- out of the TCM monad, so that we can pass it to the compilation function without pulling in the TCM Monad. Another minor
-- problem might be error reporting?
module Agda.Compiler.UHC.Compiler(compilerMain) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.ByteString.Lazy as BS
import qualified Data.Map as M
import Data.Set(Set)
import qualified Data.Set as S
import Data.Maybe
import Data.Monoid
import System.Directory ( canonicalizePath, createDirectoryIfMissing
                        , getCurrentDirectory, setCurrentDirectory
                        )
import Data.Version
import Data.List as L
import System.Exit
import System.FilePath hiding (normalise)
import System.Process hiding (env)

import Paths_Agda
import Agda.Compiler.CallCompiler
import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Interaction.Imports
import Agda.Syntax.Common (Delayed(..))
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Syntax.Internal hiding (Term(..))
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Serialise
import Agda.Utils.FileName
import qualified Agda.Utils.HashMap as HMap

import Agda.Compiler.UHC.CompileState
import Agda.Compiler.UHC.Transform
import Agda.Compiler.UHC.ModuleInfo
import Agda.Compiler.UHC.Core
import qualified Agda.Compiler.UHC.FromAgda     as FAgda
import qualified Agda.Compiler.UHC.Smashing     as Smash
import Agda.Compiler.UHC.Naming
import Agda.Compiler.UHC.AuxAST

import UHC.Util.Pretty
import UHC.Util.Serialize

import UHC.Util.AssocL
import UHC.Light.Compiler.Core.API as EC

#include "undefined.h"
import Agda.Utils.Impossible

type CoreCode = String

-- we should use a proper build system to ensure that things get only built once instead....
-- but better than nothing
type CompModT = StateT CompiledModules
type CompiledModules = M.Map ModuleName AModuleInfo

putCompModule :: Monad m => AModuleInfo -> CompModT m ()
putCompModule mod = modify (M.insert (amiModule mod) mod)

compileUHCAgdaBase :: TCM ()
compileUHCAgdaBase = do
    -- TODO we should not do this in the data directory, it may be read only...
    -- TODO only compile uhc-agda-base when we have to
    dataDir <- (</> "uhc-agda-base") <$> liftIO getDataDir
    pwd <- liftIO $ getCurrentDirectory

    -- get user package dir
    ehcBin <- getEhcBin
    (pkgSuc, pkgDbOut, _) <- liftIO $ readProcessWithExitCode ehcBin ["--meta-pkgdir-user"] ""

    case pkgSuc of
        ExitSuccess -> do
                let pkgDbDir = head $ lines pkgDbOut
                liftIO $ setCurrentDirectory dataDir

                let vers = showVersion version
                    pkgName = "uhc-agda-base-" ++ vers
                    hsFiles = ["src/UHC/Agda/Builtins.hs"]
                reportSLn "uhc" 10 $ unlines $
                    [ "Compiling " ++ pkgName ++ ", installing into package db " ++ pkgDbDir ++ "."
                    ]


                callUHC1 (  ["--odir=" ++ pkgDbDir ++""
                            , "--pkg-build=" ++ pkgName
                            , "--pkg-build-exposed=UHC.Agda.Builtins"
                            , "--pkg-expose=base-3.0.0.0"
                            ] ++ hsFiles)


                liftIO $ setCurrentDirectory pwd
        ExitFailure _ -> internalError $ unlines
            [ "Agda couldn't find the UHC user package directory."
            ]

-- | Compile an interface into an executable using Epic
compilerMain :: Interface -> TCM ()
compilerMain inter = do
    -- TODO do proper check for uhc existance
    let uhc_exist = ExitSuccess
    case uhc_exist of
        ExitSuccess -> do
            compileUHCAgdaBase

            setUHCDir inter
            modInfo <- evalStateT (compileModule inter) M.empty
            main <- getMain inter

            -- get core name from modInfo
            let crMain = cnName $ fromJust $ qnameToCoreName (amifNameMp $ amiInterface modInfo) main

            runUhcMain modInfo crMain
            return ()

        ExitFailure _ -> internalError $ unlines
           [ "Agda cannot find the UHC compiler."
--           , "This can perhaps be fixed by running `cabal install epic'."
--           , "See the README for more information."
           ]

auiFile :: CN.TopLevelModuleName -> TCM FilePath
auiFile mod = do
  let (dir, fn) = splitFileName . foldl1 (</>) $ ("Cache" : (CN.moduleNameParts mod))
      fp  | dir == "./"  = fn
          | otherwise = dir </> fn
  liftIO $ createDirectoryIfMissing True dir
  return $ fp
  where repldot c = map (\c' -> if c' == '.' then c else c')

outFile :: [String] -> TCM FilePath
outFile modParts = do
  let (dir, fn) = splitFileName $ foldl1 (</>) modParts
      fp  | dir == "./"  = fn
          | otherwise = dir </> fn
  liftIO $ createDirectoryIfMissing True dir
  return $ fp
  where repldot c = map (\c' -> if c' == '.' then c else c')

compileModule :: Interface -> CompModT TCM AModuleInfo
compileModule i = do
    -- we can't use the Core module name to get the name of the aui file,
    -- as we don't know the Core module name before we loaded/compiled the file.
    -- (well, we could just compute the module name and use that, that's
    -- probably better? )
    cm <- get
    let moduleName = iModuleName i
    let topModuleName = toTopLevelModuleName moduleName
    inFile <- lift $ findFile topModuleName
    auiFile <- lift $ auiFile topModuleName
    case M.lookup moduleName cm of
        Just x -> return x
        Nothing  -> do
            imports <- map miInterface . catMaybes
                                      <$> lift (mapM (getVisitedModule . toTopLevelModuleName . fst)
                                                     (iImportedModules i))
            modInfos <- mapM compileModule imports
            ifile <- maybe __IMPOSSIBLE__ filePath <$> lift (findInterfaceFile topModuleName)
            let uifFile = auiFile <.> "aui"
            uptodate <- liftIO $ isNewerThan uifFile ifile
            lift $ reportSLn "UHC" 15 $ "Interface file " ++ uifFile ++ " is uptodate: " ++ show uptodate
            modInfo <- case uptodate of
              True  -> do
                    lift $ reportSLn "" 5 $
                        show moduleName ++ " : UHC backend interface file is up to date."
                    uif <- lift $ readModInfoFile uifFile
                    case uif of
                      Nothing -> do
                        lift $ reportSLn "" 5 $
                            show moduleName ++ " : Could not read UHC interface file, will compile this module from scratch."
                        return Nothing
                      Just uif' -> do
                        -- now check if the versions inside modInfos match with the dep info
                        let deps = amiDepsVersion uif'
                        if depsMatch deps modInfos then do
                          lift $ reportSLn "" 1 $
                            show moduleName ++ " : module didn't change, skipping it."
                          return $ Just uif'
                        else
                          return Nothing
              False -> return Nothing

            case modInfo of
              Just x  -> putCompModule x >> return x
              Nothing -> do
                    lift $ reportSLn "" 1 $
                        "Compiling: " ++ show (iModuleName i)
                    let defns = HMap.toList $ sigDefinitions $ iSignature i
                    opts <- lift commandLineOptions
                    (code, modInfo, amod) <- lift $ compileDefns moduleName modInfos opts defns
                    lift $ do
                        let modParts = fst $ fromMaybe __IMPOSSIBLE__ $ mnameToCoreName (amiCurNameMp modInfo) moduleName
                        crFile <- outFile modParts
                        writeCoreFile crFile code
                        writeModInfoFile uifFile modInfo

                    putCompModule modInfo
                    return modInfo

  where depsMatch :: [(ModuleName, ModVersion)] -> [AModuleInfo] -> Bool
        depsMatch modDeps otherMods = all (checkDep otherMods) modDeps
        checkDep :: [AModuleInfo] -> (ModuleName, ModVersion) -> Bool
        checkDep otherMods (nm, v) = case find ((nm==) . amiModule) otherMods of
                    Just v' -> (amiVersion v') == v
                    Nothing -> False

readModInfoFile :: String -> TCM (Maybe AModuleInfo)
readModInfoFile f = do
  modInfo <- liftIO (BS.readFile f) >>= decode
  return $ maybe Nothing (\mi ->
    if amiFileVersion mi == currentModInfoVersion
        && amiAgdaVersion mi == currentInterfaceVersion then
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

-- | Perform the chain of compilation stages, from definitions to epic code
compileDefns :: ModuleName
    -> [AModuleInfo] -- ^ top level imports
    -> CommandLineOptions
    -> [(QName, Definition)] -> TCM (EC.CModule, AModuleInfo, AMod)
compileDefns mod modImps opts defs = do

    (amod', modInfo) <- FAgda.fromAgdaModule mod modImps defs $ \mod ->
                   return mod
               >>= optim optOptimSmashing "smashing"      Smash.smash'em
               >>= idPrint "done" return
    reportSLn "uhc" 10 $ "Done generating AuxAST for \"" ++ show mod ++ "\"."
    crMod <- toCore amod' modInfo modImps

    reportSLn "uhc" 10 $ "Done generating Core for \"" ++ show mod ++ "\"."
    return (crMod, modInfo, amod')
  where optim :: (CommandLineOptions -> Bool) -> String -> Transform -> Transform
        optim p s m x | p opts = idPrint s m x
                      | otherwise = return x

writeCoreFile :: String -> EC.CModule -> TCM FilePath
writeCoreFile f mod = do
  useTextual <- optUHCTextualCore <$> commandLineOptions

  -- dump textual core, useful for debugging.
  when useTextual (do
    let f' = f <.> ".dbg.tcr"
    reportSLn "uhc" 10 $ "Writing textual core to \"" ++ show f' ++ "\"."
    liftIO $ putPPFile f' (EC.printModule defaultEHCOpts mod) 200
    )

  let f' = f <.> ".bcr"
  reportSLn "uhc" 10 $ "Writing binary core to \"" ++ show f' ++ "\"."
  liftIO $ putSerializeFile f' mod
  return f'

-- | Change the current directory to Epic folder, create it if it doesn't already
--   exist.
setUHCDir :: Interface -> TCM ()
setUHCDir mainI = do
    let tm = toTopLevelModuleName $ iModuleName mainI
    f <- findFile tm
    compileDir' <- gets (fromMaybe (filePath $ CN.projectRoot f tm) .
                                  optCompileDir . stPersistentOptions . stPersistentState)
    compileDir <- liftIO $ canonicalizePath compileDir'
    liftIO $ setCurrentDirectory compileDir
    liftIO $ createDirectoryIfMissing False "UHC"
    liftIO $ setCurrentDirectory $ compileDir </> "UHC"

-- | Create the UHC Core main file, which calls the Agda main function
runUhcMain :: AModuleInfo -> HsName -> TCM ()
runUhcMain mainMod mainName = do
    let fp = "Main"
    let mod = createMainModule mainMod mainName
    fp' <- writeCoreFile fp mod
    -- TODO drop the RTS args as soon as we don't need the additional memory anymore
    callUHC1 ["--output=" ++ (show $ last $ mnameToList $ amiModule mainMod), fp', "+RTS", "-K8g", "-RTS"]

callUHC :: Bool -> FilePath -> TCM ()
callUHC isMain fp = callUHC1 $ catMaybes
    [ if isMain then Nothing else Just "--compile-only", Just fp]

callUHC1 :: [String] -> TCM ()
callUHC1 args = do
    ehcBin <- getEhcBin
    doCall <- optUHCCallUHC <$> commandLineOptions
    when doCall (callCompiler ehcBin args)

getEhcBin :: TCM FilePath
getEhcBin = fromMaybe ("uhc") . optUHCEhcBin <$> commandLineOptions

