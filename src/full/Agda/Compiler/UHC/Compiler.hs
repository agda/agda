{-# LANGUAGE CPP             #-}

-- | UHC compiler backend, main entry point.

-- In the long term, it would be nice if we could use e.g. shake to
-- build individual Agda modules. The problem with that is that some
-- parts need to be in the TCM Monad, which doesn't easily work in
-- shake. We would need a way to extract the information out of the
-- TCM monad, so that we can pass it to the compilation function
-- without pulling in the TCM Monad. Another minor problem might be
-- error reporting?

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
import Agda.Utils.Lens

import Agda.Compiler.UHC.CompileState
import Agda.Compiler.UHC.Bridge as UB
import qualified Agda.Compiler.UHC.FromAgda     as FAgda
import Agda.Compiler.Common

#include "undefined.h"
import Agda.Utils.Impossible

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
compilerMain :: IsMain -> Interface -> TCM ()
compilerMain isMain i = inCompilerEnv i $ do
    when (not uhcBackendEnabled) $ typeError $ GenericError "Agda has been built without UHC support. To use the UHC compiler you need to reinstall Agda with 'cabal install Agda -f uhc'."
    -- TODO we should do a version check here at some point.
    let uhc_exist = ExitSuccess
    case uhc_exist of
        ExitSuccess -> do

            copyUHCAgdaBase =<< compileDir

            doCompile isMain i $ \_ -> compileModule

            case isMain of
              IsMain -> do
                main <- getMain i
                -- get core name from modInfo
                crMain <- getCoreName1 main
                runUHCMain $ Just (iModuleName i, crMain)
              NotMain -> runUHCMain Nothing

        ExitFailure _ -> internalError $ unlines
           [ "Agda cannot find the UHC compiler."
           ]


-- | Compiles a module and it's imports. Returns the module info
-- of this module, and the accumulating module interface.
compileModule :: Interface -> TCM ()
compileModule i = do
    -- look for the Agda.Primitive interface in visited modules.
    -- (It will not be in ImportedModules, if it has not been
    -- explicitly imported)
    -- TODO this should be done in a more clean way
    [agdaPrimInter] <- filter (("Agda.Primitive"==) . prettyShow . iModuleName)
      . map miInterface . M.elems
        <$> getVisitedModules
    -- we can't use the Core module name to get the name of the aui file,
    -- as we don't know the Core module name before we loaded/compiled the file.
    -- (well, we could just compute the module name and use that, that's
    -- probably better? )
    let modNm = iModuleName i
    let topModuleName = toTopLevelModuleName modNm
    -- check if this module has already been compiled
    imports <- map miInterface . catMaybes
      <$> (mapM (getVisitedModule . toTopLevelModuleName . fst)
            (iImportedModules i))

    let imports' = if prettyShow (iModuleName i) == "Agda.Primitive"
                     then imports
                     else agdaPrimInter : imports

    reportSLn "compile.uhc" 1 $
      "Compiling: " ++ show (iModuleName i)
    code <- compileDefns modNm (map iModuleName imports') i
    crFile <- corePath modNm
    _ <- writeCoreFile crFile code
    return ()


corePath :: ModuleName -> TCM FilePath
corePath mName = do
  mdir <- compileDir
  let fp = mdir </> replaceExtension fp' "bcr"
  liftIO $ createDirectoryIfMissing True (takeDirectory fp)
  return fp
   where
    fp' = foldl1 (</>) $ moduleNameToCoreNameParts mName



getMain :: MonadTCM m => Interface -> m QName
getMain iface = case concatMap f defs of
    [] -> typeError $ GenericError $ "Could not find main."
    [x] -> return x
    _   -> __IMPOSSIBLE__
  where defs = HMap.toList $ iSignature iface ^. sigDefinitions
        f (qn, def) = case theDef def of
            (Function{}) | "main" == show (qnameName qn) -> [qn]
            _   -> []

-- | Perform the chain of compilation stages, from definitions to UHC Core code
compileDefns :: ModuleName
    -> [ModuleName] -- ^ top level imports
    -> Interface -> TCM UB.CModule
compileDefns modNm curModImps iface = do

    crMod <- FAgda.fromAgdaModule modNm curModImps iface

    reportSLn "compile.uhc" 10 $ "Done generating Core for \"" ++ show modNm ++ "\"."
    return crMod

writeCoreFile :: String -> UB.CModule -> TCM ()
writeCoreFile f cmod = do
  useTextual <- optUHCTextualCore <$> commandLineOptions

  -- dump textual core, useful for debugging.
  when useTextual (do
    let f' = replaceExtension f ".dbg.tcr"
    reportSLn "compile.uhc" 10 $ "Writing textual core to \"" ++ show f' ++ "\"."
    liftIO $ putPPFile f' (UB.printModule defaultEHCOpts cmod) 200
    )

  reportSLn "compile.uhc" 10 $ "Writing binary core to \"" ++ show f ++ "\"."
  liftIO $ putSerializeFile f cmod

-- | Create the UHC Core main file, which calls the Agda main function
runUHCMain
    :: Maybe (ModuleName, HsName)  -- main module
    -> TCM ()
runUHCMain mainInfo = do
    otherFps <- mapM (corePath . iModuleName . miInterface) =<< (M.elems <$> getVisitedModules)
    allFps <-
      case mainInfo of
            Nothing -> return otherFps
            Just (mainMod, mainName) -> do
                fp <- (</> "Main.bcr") <$> compileDir
                let mmod = FAgda.createMainModule mainMod mainName
                writeCoreFile fp mmod
                return ["Main.bcr"]

    let extraOpts = maybe
            ["--compile-only"]
            ((\x -> [x]) . ("--output="++) . prettyShow . last . mnameToList . fst)
            mainInfo

    liftIO . setCurrentDirectory =<< compileDir

    -- TODO drop the RTS args as soon as we don't need the additional
    -- memory anymore
    callUHC1 $  [ "--pkg-hide-all"
                , "--pkg-expose=uhcbase"
                , "--pkg-expose=base"
                , "UHC/Agda/double.c"
                ] ++ extraOpts ++ allFps ++ ["+RTS", "-K50m", "-RTS"]

callUHC1 :: [String] -> TCM ()
callUHC1 args = do
    uhcBin <- getUhcBin
    doCall <- optUHCCallUHC <$> commandLineOptions
    extraArgs <- optUHCFlags <$> commandLineOptions
    callCompiler doCall uhcBin (args ++ extraArgs)

getUhcBin :: TCM FilePath
getUhcBin = fromMaybe ("uhc") . optUHCBin <$> commandLineOptions
