{-# LANGUAGE CPP #-}

-- | Epic compiler backend.
module Agda.Compiler.Epic.Compiler(compilerMain) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State

import qualified Data.ByteString.Lazy as BS
import qualified Data.Map as Map
import Data.Maybe
import Data.Monoid
import Data.Set (Set)
import qualified Data.Set as Set

import System.Directory ( canonicalizePath, createDirectoryIfMissing
                        , getCurrentDirectory, setCurrentDirectory
                        )
import System.Exit
import System.FilePath hiding (normalise)
import System.Process hiding (env)

import Paths_Agda

import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Interaction.Imports

import Agda.Packaging.Database

import Agda.Syntax.Common (Delayed(..))
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Syntax.Internal hiding (Term(..))

import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.TypeChecking.Serialise

import Agda.Compiler.CallCompiler

import Agda.Compiler.Epic.CompileState
import qualified Agda.Compiler.Epic.CaseOpts     as COpts
import qualified Agda.Compiler.Epic.ForceConstrs as ForceC
import Agda.Compiler.Epic.Epic
import Agda.Compiler.Epic.Interface
import qualified Agda.Compiler.Epic.Erasure      as Eras
import qualified Agda.Compiler.Epic.FromAgda     as FAgda
import qualified Agda.Compiler.Epic.Forcing      as Forcing
import qualified Agda.Compiler.Epic.Injection    as ID
import qualified Agda.Compiler.Epic.NatDetection as ND
import qualified Agda.Compiler.Epic.Primitive    as Prim
import qualified Agda.Compiler.Epic.Smashing     as Smash

import Agda.Utils.FileName
import qualified Agda.Utils.HashMap as HMap
import Agda.Utils.Lens
import Agda.Utils.List
import Agda.Utils.Pretty ( prettyShow )

#include "undefined.h"
import Agda.Utils.Impossible

compilePrelude :: Compile TCM ()
compilePrelude = do
    dataDir <- (</> "EpicInclude") <$> liftIO getDataDir
    pwd <- liftIO $ getCurrentDirectory
    liftIO $ setCurrentDirectory dataDir
    let prelude = "AgdaPrelude"
    uptodate <- liftIO $ (prelude <.> "ei") `isNewerThan` (prelude <.> "e")
    when (not uptodate) $ callEpic False [ "-c" , prelude <.> "e" ]
    liftIO $ setCurrentDirectory pwd

-- | Compile an interface into an executable using Epic
compilerMain :: Interface -> TCM ()
compilerMain inter = do
    (epic_exist, _, _) <-
       liftIO $ readProcessWithExitCode
                  "ghc-pkg"
                  ["-v0", "field", "epic", "id"]
                  ""
    case epic_exist of
        ExitSuccess -> flip evalStateT initCompileState $ do
            compilePrelude
            setEpicDir inter
            (_, imports) <- compileModule inter
            main <- getMain
            runEpicMain main (Set.toList imports) (iModuleName inter)

        ExitFailure _ -> internalError $ unlines
           [ "Agda cannot find the Epic compiler."
           , "This can perhaps be fixed by running `cabal install epic'."
           , "See the README for more information."
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

readEInterface :: FilePath -> Compile TCM EInterface
readEInterface file = fromMaybe __IMPOSSIBLE__
                   <$> lift (decode =<< liftTCM (liftIO (BS.readFile file)))

compileModule :: Interface -> Compile TCM (EInterface, Set FilePath)
compileModule i = do
    cm <- gets compiledModules
    let moduleName = toTopLevelModuleName $ iModuleName i
    file  <- outFile moduleName
    case Map.lookup moduleName cm of
        Just eifs -> return eifs
        Nothing  -> do
            imports <- map miInterface . catMaybes
                                      <$> mapM (lift . getVisitedModule . toTopLevelModuleName . fst)
                                               (iImportedModules i)
            (ifaces, limps) <- mapAndUnzipM compileModule imports
            let imps = Set.unions limps
            modify $ \s -> s { importedModules = importedModules s `mappend` mconcat ifaces }
            ifile <- maybe __IMPOSSIBLE__ filePath <$> lift (traverse asAbsolutePath =<< findInterfaceFile moduleName)
            let eifFile = file <.> "aei"
            uptodate <- liftIO $ isNewerThan eifFile ifile
            (eif, imps') <- case uptodate of
                True  -> do
                    lift $ reportSLn "" 1 $
                      (prettyShow . iModuleName) i ++ " : no compilation is needed."
                    eif <- readEInterface eifFile
                    modify $ \s -> s { curModule = eif }
                    return (eif, Set.insert file imps)
                False -> do
                    lift $ reportSLn "" 1 $
                        "Compiling: " ++ (prettyShow . iModuleName) i
                    resetNameSupply
                    initialAnalysis i
                    let defns = HMap.toList $ iSignature i ^. sigDefinitions
                    -- Epic cannot parse files with no definitions
                    if (not $ null defns) then do
                        code <- compileDefns defns
                        runEpic file (Set.toList imps) code
                        eif <- gets curModule
                        lift $ do
                            bif <- encode eif
                            liftIO $ BS.writeFile eifFile bif
                        return (eif, Set.insert file imps)
                     else
                        flip (,) imps <$> gets curModule
            modify $ \s -> s { compiledModules = (Map.insert moduleName (eif, imps') (compiledModules s))}
            return (eif, imps')

-- | Before running the compiler, we need to store some things in the state,
--   namely constructor tags, constructor irrelevancies and the delayed field
--   in functions (for coinduction).
initialAnalysis :: Interface -> Compile TCM ()
initialAnalysis inter = do
  Prim.initialPrims
  modify $ \s -> s {curModule = mempty}
  let defs = HMap.toList $ iSignature inter ^. sigDefinitions
  forM_ defs $ \(q, def) -> do
    addDefName q
    case theDef def of
      d@(Datatype {}) -> do
        saker <- ND.isNatish q d
        case saker of
            Just (_, [zer, suc]) -> do
                putConstrTag zer (PrimTag "primZero")
                putConstrTag suc (PrimTag "primSuc")
            _ -> return ()
      Constructor {conPars = np} -> do
        putForcedArgs q . drop np . ForceC.makeForcedArgs $ defType def
        putConArity q =<< lift (constructorArity q)
      f@(Function{}) -> do
        when ("main" == (prettyShow . qnameName) q) $ do
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

idPrint :: String -> (a -> Compile TCM b) -> a -> Compile TCM b
idPrint s m x = do
  lift $ reportSLn "epic.phases" 10 s
  m x

-- | Perform the chain of compilation stages, from definitions to epic code
compileDefns :: [(QName, Definition)] -> Compile TCM EpicCode
compileDefns defs = do
    -- We need to handle sharp (coinduction) differently, so we get it here.
    msharp <- lift $ getBuiltin' builtinSharp
    emits   <- return defs
               >>= idPrint "findInjection" ID.findInjection
               >>= idPrint "fromAgda"   (FAgda.fromAgda msharp)
               >>= idPrint "forcing"     Forcing.remForced
               >>= idPrint "irr"         ForceC.forceConstrs
               >>= idPrint "primitivise" Prim.primitivise
               >>= idPrint "smash"       Smash.smash'em
               >>= idPrint "erasure"     Eras.erasure
               >>= idPrint "caseOpts"    COpts.caseOpts
               >>= idPrint "done" return
    unlines <$> mapM prettyEpicFun emits

-- | Change the current directory to Epic folder, create it if it doesn't already
--   exist.
setEpicDir :: Interface -> Compile (TCMT IO) ()
setEpicDir mainI = do
    let tm = toTopLevelModuleName $ iModuleName mainI
    f <- lift $ asAbsolutePath =<< findFile tm
    compileDir' <- lift $ gets (fromMaybe (filePath $ CN.projectRoot f tm) .
                                  optCompileDir . stPersistentOptions . stPersistentState)
    compileDir <- liftIO $ canonicalizePath compileDir'
    liftIO $ setCurrentDirectory compileDir
    liftIO $ createDirectoryIfMissing False "Epic"
    liftIO $ setCurrentDirectory $ compileDir </> "Epic"

-- | Make a program from the given Epic code.
--
-- The program is written to the file @../m@, where m is the last
-- component of the given module name.
runEpic :: FilePath -> [FilePath] -> EpicCode -> Compile TCM ()
runEpic fp imports code = do
    dataDir <- (</> "EpicInclude") <$> liftIO getDataDir
    let imports' = unlines ["include \"" ++ imp ++ "\""
                           | imp <- (dataDir </> "AgdaPrelude.ei")
                                    : map (<.> "ei") imports]
        code'    = imports' ++ code
    liftIO $ writeFile (fp <.> "e") code'
    callEpic True $
        [ "-c", fp <.> "e" ]

-- | Create the Epic main file, which calls the Agda main function
runEpicMain :: Var -> [FilePath] -> ModuleName -> Compile TCM ()
runEpicMain mainName imports m = do
    dataDir <- (</> "EpicInclude") <$> liftIO getDataDir
    let imports' = (dataDir </> "AgdaPrelude") : imports
    let code = unlines ["include \"" ++ imp <.> "ei" ++ "\""
                       | imp <- imports'
                       ] ++ "main() -> Unit = init() ; " ++ mainName ++ "(unit)"
    liftIO $ writeFile ("main" <.> "e") code

    let outputName :: CN.Name
        outputName = maybe __IMPOSSIBLE__ nameConcrete $ lastMaybe $ mnameToList m

    callEpic'  $ \epic ->
        [ "main" <.> "e"
        , "-o", ".." </> prettyShow outputName
        ]
        ++ epic ++ map (<.> "o") imports'

-- | Call epic, with a given set of flags, if the |Bool| is True then include
-- the command line flags at the end
callEpic :: Bool -> [String] -> Compile TCM ()
callEpic incEFlags flags = callEpic' $ \epicFlags ->
  flags ++ if incEFlags then epicFlags else []

-- | Call epic with a given set of flags, the argument function receives the flags given
-- at the command line
callEpic' :: ([String] -> [String]) -> Compile TCM ()
callEpic' flags = do
    epicFlags <- optEpicFlags <$> lift commandLineOptions
    dataDir   <- (</> "EpicInclude") <$> liftIO getDataDir
    let epic        = "epic"
        epicCommand =
          [ "-keepc"
          -- , "-g"
          -- , "-checking", "0"
          -- , "-trace"
          , "-i", dataDir </> "stdagda" <.> "c"
          ] ++ flags epicFlags

    lift $ callCompiler True epic epicCommand
