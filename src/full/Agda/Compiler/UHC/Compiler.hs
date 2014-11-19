{-# LANGUAGE CPP, DoAndIfThenElse #-}
-- | UHC compiler backend.
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

#ifdef UHC_BACKEND
import Agda.Compiler.UHC.CompileState
import Agda.Compiler.UHC.ModuleInfo
--import qualified Agda.Compiler.UHC.CaseOpts     as COpts
--import qualified Agda.Compiler.UHC.ForceConstrs as ForceC
import Agda.Compiler.UHC.Core
import qualified Agda.Compiler.UHC.FromAgda     as FAgda
--import qualified Agda.Compiler.UHC.Forcing      as Forcing
--import qualified Agda.Compiler.UHC.Injection    as ID
--import qualified Agda.Compiler.UHC.NatDetection as ND
--import qualified Agda.Compiler.UHC.Primitive    as Prim
--import qualified Agda.Compiler.UHC.Smashing     as Smash
import Agda.Compiler.UHC.Naming
import Agda.Compiler.UHC.AuxAST

import UHC.Util.Pretty
import UHC.Util.Serialize

import UHC.Util.AssocL
import UHC.Light.Compiler.Core.API as EC

#include "undefined.h"
import Agda.Utils.Impossible

type CoreCode = String

compileUHCAgdaBase :: TCM ()
compileUHCAgdaBase = do

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


                -- TODO should we pass pkg-build-depends as well?
                callUHC1 (  ["--odir=" ++ pkgDbDir ++""
                            , "--pkg-build=" ++ pkgName
                            , "--pkg-build-exposed=UHC.Agda.Builtins"
                            , "--pkg-expose=base-3.0.0.0"
{-                            , "--pkg-expose=uhcbase-1.1.7.0"-}] ++ hsFiles)


                liftIO $ setCurrentDirectory pwd
        ExitFailure _ -> internalError $ unlines
            [ "Agda couldn't find the UHC user package directory."
            ]
    {-
    uptodate <- liftIO $ (prelude <.> "ei") `isNewerThan` (prelude <.> "e")
    when (not uptodate) $ callEpic False [ "-c" , prelude <.> "e" ]-}

-- | Compile an interface into an executable using Epic
compilerMain :: Interface -> TCM ()
compilerMain inter = do
{-    (epic_exist, _, _) <-
       liftIO $ readProcessWithExitCode
                  "ghc-pkg"
                  ["-v0", "field", "epic", "id"]
                  ""-}

    let epic_exist = ExitSuccess -- PH TODO do check for uhc
    case epic_exist of
        ExitSuccess -> do
            compileUHCAgdaBase

            setUHCDir inter
            modInfo <- compileModule inter
            main <- getMain inter

            -- get core name from modInfo
            let crMain = cnName $ fromJust $ qnameToCoreName (amifNameMp $ amiInterface modInfo) main

            runUhcMain crMain (iModuleName inter)
            return ()

        ExitFailure _ -> internalError $ unlines
           [ "Agda cannot find the UHC compiler."
--           , "This can perhaps be fixed by running `cabal install epic'."
--           , "See the README for more information."
           ]

outFile :: CN.TopLevelModuleName -> TCM FilePath
outFile mod = do
  let (dir, fn) = splitFileName . foldl1 (</>) $ CN.moduleNameParts mod
      fp  | dir == "./"  = fn
          | otherwise = dir </> fn
  liftIO $ createDirectoryIfMissing True dir
  return $ fp
  where repldot c = map (\c' -> if c' == '.' then c else c')

compileModule :: Interface -> TCM AModuleInfo
compileModule i = do
--    cm <- gets compiledModules
    let moduleName = iModuleName i
    let topModuleName = toTopLevelModuleName moduleName
    file  <- outFile topModuleName
--    case M.lookup moduleName cm of
    case Nothing of
        Just x -> __IMPOSSIBLE__
--        Just eifs -> return eifs
        Nothing  -> do
            imports <- map miInterface . catMaybes
                                      <$> mapM (getVisitedModule . toTopLevelModuleName . fst)
                                               (iImportedModules i)
            modInfos <- mapM compileModule imports
--            let imps = S.unions limps
--            modify $ \s -> s { importedModules = importedModules s `mappend` mconcat ifaces }
--            ifile <- maybe __IMPOSSIBLE__ filePath <$> lift (findInterfaceFile moduleName)
--            let eifFile = file <.> "aei"
--            uptodate <- liftIO $ isNewerThan eifFile ifile
-- PH : TODO see missing instance problem in readEInterface
{-            (eif, imps') <- case uptodate of
                True  -> do
                    lift $ reportSLn "" 1 $
                        show (iModuleName i) ++ " : no compilation is needed."
                    eif <- readEInterface eifFile
                    modify $ \s -> s { curModule = eif }
                    return (eif, S.insert file imps)
                False -> do-}
            modInfo <- do
                    reportSLn "" 1 $
                        "Compiling: " ++ show (iModuleName i)
--                    initialAnalysis i
                    let defns = HMap.toList $ sigDefinitions $ iSignature i
                    (code, modInfo, amod) <- compileDefns moduleName modInfos defns

                    runUHC file code
--                    eif <- gets curModule
                    return modInfo
            return modInfo


getMain :: MonadTCM m => Interface -> m QName
getMain iface = case concatMap f defs of
    [] -> typeError $ GenericError $ "Could not find main."
    [x] -> return x
    _   -> __IMPOSSIBLE__
  where defs = HMap.toList $ sigDefinitions $ iSignature iface
        f (qn, def) = case theDef def of
            (Function{}) | "main" == show (qnameName qn) -> [qn]
            _   -> []

-- | Before running the compiler, we need to store some things in the state,
--   namely constructor tags, constructor irrelevancies and the delayed field
--   in functions (for coinduction).
{-initialAnalysis :: Interface -> TCM ()
initialAnalysis inter = do
-- TODO PH : fix natish
--  Prim.initialPrims
  modify $ \s -> s {curModule = mempty}
  let defs = HMap.toList $ sigDefinitions $ iSignature inter
  forM_ defs $ \(q, def) -> do
    addDefName q
    case theDef def of
      d@(Datatype {}) -> do
        return ()
        -- TODO PH : fix natish
--        saker <- ND.isNatish q d
{-        case saker of
            Just (_, [zer, suc]) -> do
                putConstrTag zer (PrimTag "primZero")
                putConstrTag suc (PrimTag "primSuc")
             _ -> return () -}
      Constructor {conPars = np} -> do
--        putForcedArgs q . drop np . ForceC.makeForcedArgs $ defType def
        putConArity q =<< lift (constructorArity q)
      f@(Function{}) -> do
        when ("main" == show (qnameName q)) $ do
            -- lift $ liftTCM $ checkTypeOfMain q (defType def)
            putMain q
        putDelayed q $ case funDelayed f of
          Delayed -> True
          NotDelayed -> False
      a@(Axiom {}) -> do
        case defEpicDef def of
          Nothing -> putDelayed q True
          _       -> return ()
      _ -> return ()
-}

idPrint :: String -> (a -> TCM b) -> a -> TCM b
idPrint s m x = do
  reportSLn "uhc.phases" 10 s
  m x

-- | Perform the chain of compilation stages, from definitions to epic code
compileDefns :: ModuleName
    -> [AModuleInfo] -- ^ top level imports
    -> [(QName, Definition)] -> TCM (EC.CModule, AModuleInfo, AMod)
compileDefns mod modImps defs = do
    -- We need to handle sharp (coinduction) differently, so we get it here.
    msharp <- getBuiltin' builtinSharp
--    let modName = L.intercalate "." (CN.moduleNameParts mod)

    (amod, modInfo) <- idPrint "fromAgda" (FAgda.fromAgdaModule msharp mod modImps) defs
    amod'   <- return amod
--               >>= idPrint "findInjection" ID.findInjection
--               >>= idPrint "fromAgda"   (FAgda.fromAgdaModule msharp modName modImps)
--               >>= idPrint "forcing"     Forcing.remForced
--               >>= idPrint "irr"         ForceC.forceConstrs
--               >>= idPrint "primitivise" Prim.primitivise
--               >>= idPrint "smash"       Smash.smash'em
--               >>= idPrint "erasure"     Eras.erasure
--               >>= idPrint "caseOpts"    COpts.caseOpts
               >>= idPrint "done" return
    reportSLn "uhc" 10 $ "Done generating AuxAST for \"" ++ show mod ++ "\"."
    crMod <- toCore amod' modInfo modImps
--    let modEntRel =  getExportedExprs modInfo
    reportSLn "uhc" 10 $ "Done generating Core for \"" ++ show mod ++ "\"."
    return (crMod, modInfo, amod')

writeCoreFile :: String -> EC.CModule -> TCM FilePath
writeCoreFile f mod = do
  useTextual <- optUHCTextualCore <$> commandLineOptions

  -- dump textual core, useful for debugging.
  when useTextual (do
    let f' = f <.> ".tcr"
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

-- | Make a program from the given Epic code.
--
-- The program is written to the file @../m@, where m is the last
-- component of the given module name.
runUHC :: FilePath -> EC.CModule -> TCM ()
runUHC fp code = do
    fp' <- writeCoreFile fp code
--    liftIO $ putSerializeFile (fp <.> "hi") hi
    -- this is a hack, fix this for supporting multiple agda modules
    callUHC False fp'

-- | Create the Epic main file, which calls the Agda main function
runUhcMain :: HsName -> ModuleName -> TCM ()
runUhcMain mainName modNm = do
    let fp = "Main"
    let mod = createMainModule (show modNm) mainName
    fp' <- writeCoreFile fp mod

    callUHC True fp'

callUHC :: Bool -> FilePath -> TCM ()
callUHC isMain fp = callUHC1 $ catMaybes
    [ if isMain then Nothing else Just "--compile-only"
    , Just fp]

callUHC1 :: [String] -> TCM ()
callUHC1 args = do
    ehcBin <- getEhcBin
    doCall <- optUHCCallUHC <$> commandLineOptions
    when doCall (callCompiler ehcBin args)

getEhcBin :: TCM FilePath
getEhcBin = fromMaybe ("ehc") . optUHCEhcBin <$> commandLineOptions

#else

-- UHC backend has not been compiled
compilerMain :: Interface -> TCM ()
compilerMain inter = error "UHC Backend disabled."

#endif
