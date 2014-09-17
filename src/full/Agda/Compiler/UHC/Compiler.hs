{-# LANGUAGE CPP, DoAndIfThenElse #-}
-- | Epic compiler backend.
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

import Agda.Compiler.UHC.Interface

#ifdef UHC_BACKEND
import Agda.Compiler.UHC.CompileState
--import qualified Agda.Compiler.UHC.CaseOpts     as COpts
import qualified Agda.Compiler.UHC.ForceConstrs as ForceC
import Agda.Compiler.UHC.Core
import qualified Agda.Compiler.UHC.Erasure      as Eras
import qualified Agda.Compiler.UHC.FromAgda     as FAgda
import qualified Agda.Compiler.UHC.Forcing      as Forcing
--import qualified Agda.Compiler.UHC.Injection    as ID
--import qualified Agda.Compiler.UHC.NatDetection as ND
--import qualified Agda.Compiler.UHC.Primitive    as Prim
--import qualified Agda.Compiler.UHC.Smashing     as Smash
import Agda.Compiler.UHC.CoreSyntax (ehcOpts)

import UHC.Util.Pretty
import UHC.Util.Serialize

import qualified EH99.Core as EC
import qualified EH99.Core.Pretty as EP
import qualified EH99.Opts as EO

#include "../../undefined.h"
import Agda.Utils.Impossible

type CoreCode = String

compileUHCAgdaBase :: Compile TCM ()
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
                lift $ reportSLn "uhc" 10 $ unlines $
                    [ "Compiling " ++ pkgName ++ ", installing into package db " ++ pkgDbDir ++ "."
                    ]


                -- TODO should we pass pkg-build-depends as well?
                callUHC1 (  ["--odir=" ++ pkgDbDir ++""
                            , "--pkg-build=" ++ pkgName
                            , "--pkg-build-exposed=UHC.Agda.Builtins"
                            , "--pkg-expose=base-3.0.0.0"
{-                            , "--pkg-expose=uhcbase-1.1.7.0"-}] ++ hsFiles)


                liftIO $ setCurrentDirectory pwd
        ExitFailure _ -> lift $ internalError $ unlines
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
        ExitSuccess -> flip evalStateT initCompileState $ do
            compileUHCAgdaBase

            setUHCDir inter
            (_, imports) <- compileModule inter
            main <- getMain
            runUhcMain main (S.toList imports) (iModuleName inter)

        ExitFailure _ -> internalError $ unlines
           [ "Agda cannot find the UHC compiler."
--           , "This can perhaps be fixed by running `cabal install epic'."
--           , "See the README for more information."
           ]

outFile :: CN.TopLevelModuleName -> Compile TCM FilePath
outFile mod = do
  let (dir, fn) = splitFileName . foldl1 (</>) $ CN.moduleNameParts mod
      fp  | dir == "./"  = "src" </> fn
          | otherwise = "src" </> dir </> fn
  liftIO $ createDirectoryIfMissing True ("src" </> dir)
  return $ fp
  where
  repldot c = map (\c' -> if c' == '.' then c else c')

{-
 - PH: TODO fix missing instance error (did that code actually compile for the epic backend?)
readEInterface :: FilePath -> Compile TCM EInterface
readEInterface file = fromMaybe __IMPOSSIBLE__
                   <$> lift (decode =<< liftTCM (liftIO (BS.readFile file)))
-}

compileModule :: Interface -> Compile TCM (EInterface, Set FilePath)
compileModule i = do
    cm <- gets compiledModules
    let moduleName = toTopLevelModuleName $ iModuleName i
    file  <- outFile moduleName
    case M.lookup moduleName cm of
        Just eifs -> return eifs
        Nothing  -> do
            imports <- map miInterface . catMaybes
                                      <$> mapM (lift . getVisitedModule . toTopLevelModuleName . fst)
                                               (iImportedModules i)
            (ifaces, limps) <- mapAndUnzipM compileModule imports
            let imps = S.unions limps
            modify $ \s -> s { importedModules = importedModules s `mappend` mconcat ifaces }
            ifile <- maybe __IMPOSSIBLE__ filePath <$> lift (findInterfaceFile moduleName)
            let eifFile = file <.> "aei"
            uptodate <- liftIO $ isNewerThan eifFile ifile
-- PH : TODO see missing instance problem in readEInterface
{-            (eif, imps') <- case uptodate of
                True  -> do
                    lift $ reportSLn "" 1 $
                        show (iModuleName i) ++ " : no compilation is needed."
                    eif <- readEInterface eifFile
                    modify $ \s -> s { curModule = eif }
                    return (eif, S.insert file imps)
                False -> do-}
            (eif, imps') <- do
                    lift $ reportSLn "" 1 $
                        "Compiling: " ++ show (iModuleName i)
                    resetNameSupply
                    initialAnalysis i
                    let defns = HMap.toList $ sigDefinitions $ iSignature i
                    -- Epic cannot parse files with no definitions
                    if (not $ null defns) then do
                        code <- compileDefns moduleName defns
            	        -- HACK
                        runUHC file (S.toList imps) code
                        eif <- gets curModule
-- PH : TODO see missing instance problem in readEInterface
{-                        lift $ do
                            bif <- encode eif
                            liftIO $ BS.writeFile eifFile bif-}
                        return (eif, S.insert file imps)
                     else
                        flip (,) imps <$> gets curModule
            modify $ \s -> s { compiledModules = (M.insert moduleName (eif, imps') (compiledModules s))}
            return (eif, imps')

-- | Before running the compiler, we need to store some things in the state,
--   namely constructor tags, constructor irrelevancies and the delayed field
--   in functions (for coinduction).
initialAnalysis :: Interface -> Compile TCM ()
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

idPrint s m x = do
  lift $ reportSLn "epic.phases" 10 s
  m x

-- | Perform the chain of compilation stages, from definitions to epic code
compileDefns :: CN.TopLevelModuleName -> [(QName, Definition)] -> Compile TCM EC.CModule
compileDefns mod defs = do
    -- We need to handle sharp (coinduction) differently, so we get it here.
    msharp <- lift $ getBuiltin' builtinSharp
    let modName = L.intercalate "." (CN.moduleNameParts mod)
    amod   <- return defs
--               >>= idPrint "findInjection" ID.findInjection
               >>= idPrint "fromAgda"   (FAgda.fromAgdaModule msharp modName)
--               >>= idPrint "forcing"     Forcing.remForced
--               >>= idPrint "irr"         ForceC.forceConstrs
--               >>= idPrint "primitivise" Prim.primitivise
--               >>= idPrint "smash"       Smash.smash'em
--               >>= idPrint "erasure"     Eras.erasure
--               >>= idPrint "caseOpts"    COpts.caseOpts
               >>= idPrint "done" return
    lift $ reportSLn "uhc" 10 $ "Done generating AuxAST for \"" ++ show mod ++ "\"."
    crMod <- toCore amod
    lift $ reportSLn "uhc" 10 $ "Done generating Core for \"" ++ show mod ++ "\"."
    return crMod

writeCoreFile :: String -> EC.CModule -> Compile TCM FilePath
writeCoreFile f mod = do
  useTextual <- optUHCTextualCore <$> lift commandLineOptions
  let f' = takeDirectory f </> "AgdaPU." ++ takeFileName f
  if useTextual then do
    let f'' = f' <.> ".tcr"
    lift $ reportSLn "uhc" 10 $ "Writing textual core to \"" ++ show f'' ++ "\"."
    liftIO $ putPPFile f'' (EP.ppCModule ehcOpts mod) 200
    return f''
  else do
    let f'' = f' <.> ".bcr"
    lift $ reportSLn "uhc" 10 $ "Writing binary core to \"" ++ show f'' ++ "\"."
    liftIO $ putSerializeFile f'' mod
    return f''

-- | Change the current directory to Epic folder, create it if it doesn't already
--   exist.
setUHCDir :: Interface -> Compile (TCMT IO) ()
setUHCDir mainI = do
    let tm = toTopLevelModuleName $ iModuleName mainI
    f <- lift $ findFile tm
    compileDir' <- lift $ gets (fromMaybe (filePath $ CN.projectRoot f tm) .
                                  optCompileDir . stPersistentOptions . stPersistent)
    compileDir <- liftIO $ canonicalizePath compileDir'
    liftIO $ setCurrentDirectory compileDir
    liftIO $ createDirectoryIfMissing False "UHC"
    liftIO $ setCurrentDirectory $ compileDir </> "UHC"

-- | Make a program from the given Epic code.
--
-- The program is written to the file @../m@, where m is the last
-- component of the given module name.
runUHC :: FilePath -> [FilePath] -> EC.CModule -> Compile TCM ()
runUHC fp imports code = do
{-    dataDir <- (</> "EpicInclude") <$> liftIO getDataDir
    let imports' = unlines ["include \"" ++ imp ++ "\""
                           | imp <- (dataDir </> "AgdaPrelude.ei")
                                    : map (<.> "ei") imports]
        code'    = imports' ++ code-}
    fp' <- writeCoreFile fp code
    -- this is a hack, fix this for supporting multiple agda modules
    callUHC fp'
{-    callEpic True $
        [ "-c", fp <.> "e" ]-}

-- | Create the Epic main file, which calls the Agda main function
runUhcMain :: AName -> [FilePath] -> ModuleName -> Compile TCM ()
runUhcMain mainName imports m = do
    return ()
{-    dataDir <- (</> "EpicInclude") <$> liftIO getDataDir
    let imports' = (dataDir </> "AgdaPrelude") : imports
    let code = unlines ["include \"" ++ imp <.> "ei" ++ "\""
                       | imp <- imports'
                       ] ++ "main() -> Unit = init() ; " ++ mainName ++ "(unit)"-}
--    liftIO $ writeCpreFile ("main" <.> "tcr") code
{-    let outputName  = case mnameToList m of
          [] -> __IMPOSSIBLE__
          ms -> last ms
    callEpic'  $ \epic ->
        [ "main" <.> "e"
        , "-o", ".." </> show outputName
        ]
        ++ epic ++ map (<.> "o") imports'-}

callUHC :: FilePath -> Compile TCM ()
callUHC fp = callUHC1 [fp]

callUHC1 :: [String] -> Compile TCM ()
callUHC1 args = do
    ehcBin <- getEhcBin
    lift $ callCompiler ehcBin args

getEhcBin :: Compile TCM FilePath
getEhcBin = fromMaybe ("ehc") . optUHCEhcBin <$> lift commandLineOptions

#else

-- UHC backend has not been compiled
compilerMain :: Interface -> TCM ()
compilerMain inter = error "UHC Backend disabled."

#endif
