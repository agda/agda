{-# LANGUAGE CPP #-}
-- | Epic compiler backend.
module Agda.Compiler.Epic.Compiler(compilerMain) where

import Control.Applicative
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as M
import Data.Maybe
import System.Directory
import System.Exit
import System.FilePath hiding (normalise)
import System.Process hiding (env)

import Paths_Agda
import Agda.Interaction.FindFile
import Agda.Interaction.Options
import qualified Agda.Syntax.Concrete.Name as CN
import Agda.Syntax.Internal hiding (Term(..))
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Monad.Builtin
import Agda.Utils.FileName

import Agda.Compiler.Epic.CompileState hiding (conPars)
import qualified Agda.Compiler.Epic.ConstructorIrrelevancy as CIrr
import Agda.Compiler.Epic.Epic
import qualified Agda.Compiler.Epic.Erasure as Eras
import qualified Agda.Compiler.Epic.FromAgda as FAgda
import qualified Agda.Compiler.Epic.LambdaLift as LL
import qualified Agda.Compiler.Epic.Primitive  as Prim

#include "../../undefined.h"
import Agda.Utils.Impossible

-- | Compile an interface into an Epic/a.out program
--   /actually this is not true, we compile everything so we don't even look at
--   the Interface. This may change in the future.
compilerMain :: Interface -> TCM ()
compilerMain inter = do
    epic_exist <- liftIO $ rawSystem "ghc-pkg" ["-v0", "field", "epic", "id"]
    case epic_exist of
        ExitSuccess -> flip evalStateT initCompileState $ do
            setEpicDir inter
            initialAnalysis
            code <- compileModule =<< lift (gets stImports)
            case code of
                Nothing -> __IMPOSSIBLE__
                Just c  -> runEpic (iModuleName inter) c
        ExitFailure _ -> internalError $ unlines
           [ "Agda cannot find the Epic compiler."
           , "This can perhaps be fixed by running `cabal install epic'."
           , "See the README for more information."
           ]


-- | Before running the compiler, we need to store some things in the state,
--   namely constructor tags, constructor irrelevancies and the delayed field
--   in functions (for coinduction).
initialAnalysis :: Compile TCM ()
initialAnalysis = do
  defs <- M.toList <$> lift (gets (sigDefinitions . stImports))
  forM_ defs $ \(q, def) -> do
    addDefName q
    case theDef def of
      d@(Datatype {}) -> do
        addDataDecl $ dataCons d
      Constructor {conPars = np} -> do
        putIrrFilter q . drop (fromIntegral np) . CIrr.irrFilter $ defType def
        putConPar q =<< lift (constructorArity q)
      r@(Record{}) -> do
        addDataDecl [recCon r]
      f@(Function{}) -> do
        putDelayed q $ case funDelayed f of
          Delayed -> True
          NotDelayed -> False
      _ -> return ()

-- | Perform the chain of compilation stages, from definitions to epic code
compileDefns :: [(QName, Definition)] -> Compile TCM (Maybe EpicCode)
compileDefns defs = do
    -- We need to handle sharp (coinduction) differently, so we get it here.
    msharp <- lift $ getBuiltin' builtinSharp
    emits   <- FAgda.fromAgda msharp defs
               >>= Prim.primitivise
               >>= irr -- CIrr.constrIrr
               >>= Eras.erasure
               >>= LL.lambdaLift
    if null emits
       then return Nothing
       else return . return . unlines . map prettyEpicFun $ emits
  where
    irr ds = do
        f <- lift $ gets (optForcing . stPersistentOptions)
        if f then CIrr.constrIrr ds
             else return ds

-- | Compile all definitions from a signature
compileModule :: Signature -> Compile TCM (Maybe EpicCode)
compileModule sig = do
    let defs = M.toList $ sigDefinitions sig
    compileDefns defs

-- | Change the current directory to Epic folder, create it if it doesn't already
--   exist.
setEpicDir :: Interface -> Compile (TCMT IO) ()
setEpicDir mainI = do
    let tm = toTopLevelModuleName $ iModuleName mainI
    f <- lift $ findFile tm
    compileDir' <- lift $ gets (fromMaybe (filePath $ CN.projectRoot f tm) . optCompileDir . stPersistentOptions)
    compileDir <- liftIO $ canonicalizePath compileDir'
    liftIO $ setCurrentDirectory compileDir
    liftIO $ createDirectoryIfMissing False "Epic"
    liftIO $ setCurrentDirectory $ compileDir </> "Epic"

-- | Make a program from the given Epic code.
--
-- The program is written to the file @../m@, where m is the last
-- component of the given module name.
runEpic :: ModuleName -> EpicCode -> Compile TCM ()
runEpic m code = do
    nam <- getMain
    epicflags <- optEpicFlags <$> lift commandLineOptions
    let code' = "include \"AgdaPrelude.e\"\n" ++ code ++ "main() -> Unit = init() ; " ++ nam ++ "(unit)"
    dataDir <- liftIO getDataDir
    curDir  <- liftIO getCurrentDirectory
    liftIO $ copyFile (dataDir </> "EpicInclude" </> "AgdaPrelude" <.> "e")
                      (curDir </> "AgdaPrelude" <.> "e")
    liftIO $ writeFile ("main" <.> "e") code'

    let outputName  = case mnameToList m of
          [] -> __IMPOSSIBLE__
          ms -> last ms
        epic        = "epic"
        epicCommand =
          [ "-keepc"
          , "-checking", "0"
          -- , "-trace"
          , "-i", dataDir </> "EpicInclude" </> "stdagda" <.> "c"
          , "main" <.> "e"
          , "-o", ".." </> show outputName
          ] ++ epicflags
    lift $ reportSLn "" 1 $
      "calling: " ++ unwords (epic : epicCommand)
    _ <- liftIO $ rawSystem epic epicCommand
    return ()
