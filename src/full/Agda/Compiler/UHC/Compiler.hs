{-# LANGUAGE CPP             #-}

-- | UHC compiler backend, main entry point.

-- In the long term, it would be nice if we could use e.g. shake to
-- build individual Agda modules. The problem with that is that some
-- parts need to be in the TCM Monad, which doesn't easily work in
-- shake. We would need a way to extract the information out of the
-- TCM monad, so that we can pass it to the compilation function
-- without pulling in the TCM Monad. Another minor problem might be
-- error reporting?

module Agda.Compiler.UHC.Compiler (uhcBackend) where

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
import Agda.Utils.Monad

import Agda.Compiler.UHC.CompileState
import Agda.Compiler.UHC.Bridge as UB
import qualified Agda.Compiler.UHC.FromAgda     as FAgda
import Agda.Compiler.Common
import Agda.Compiler.Backend

#include "undefined.h"
import Agda.Utils.Impossible

-- Backend callbacks ------------------------------------------------------

uhcBackend :: Backend
uhcBackend = Backend uhcBackend'

uhcBackend' :: Backend' UHCOptions UHCOptions UHCModuleEnv () ()
uhcBackend' = Backend'
  { backendName    = "UHC"
  , backendVersion = Nothing
  , options          = defaultUHCOptions
  , commandLineFlags = uhcCommandLineFlags
  , isEnabled        = optUHCCompile
  , preCompile       = uhcPreCompile
  , postCompile      = uhcPostCompile
  , preModule        = uhcPreModule
  , postModule       = uhcPostModule      -- We do all compilation in postModule
  , compileDef       = \ _ _ _ -> return ()
  }

--- Options ---

data UHCOptions = UHCOptions
  { optUHCCompile     :: Bool
  , optUHCBin         :: Maybe FilePath
  , optUHCTextualCore :: Bool
  , optUHCCallUHC     :: Bool
  , optUHCTraceLevel  :: Int
  , optUHCFlags       :: [String]
  }

defaultUHCOptions :: UHCOptions
defaultUHCOptions = UHCOptions
  { optUHCCompile     = False
  , optUHCBin         = Nothing
  , optUHCTextualCore = False
  , optUHCCallUHC     = True
  , optUHCTraceLevel  = 0
  , optUHCFlags       = []
  }

uhcCommandLineFlags :: [OptDescr (Flag UHCOptions)]
uhcCommandLineFlags =
    [ Option []     ["uhc"] (NoArg compileUHCFlag) "compile program using the UHC backend"
    , Option []     ["uhc-bin"] (ReqArg uhcBinFlag "UHC") "The uhc binary to use when compiling with the UHC backend."
    , Option []     ["uhc-textual-core"] (NoArg uhcTextualCoreFlag) "Use textual core as intermediate representation instead of binary core."
    , Option []     ["uhc-dont-call-uhc"] (NoArg uhcDontCallUHCFlag) "Don't call uhc, just write the UHC Core files."
    , Option []     ["uhc-gen-trace"] (ReqArg uhcTraceLevelFlag "TRACE") "Add tracing code to generated executable."
    , Option []     ["uhc-flag"] (ReqArg uhcFlagsFlag "UHC-FLAG")
                    "give the flag UHC-FLAG to UHC when compiling using the UHC backend"
    ]
  where
    compileUHCFlag o      = return $ o { optUHCCompile = True}
    uhcBinFlag s o        = return $ o { optUHCBin  = Just s }
    uhcTextualCoreFlag o  = return $ o { optUHCTextualCore = True }
    uhcDontCallUHCFlag o  = return $ o { optUHCCallUHC = False }
    -- TODO proper parsing and error handling
    uhcTraceLevelFlag i o = return $ o { optUHCTraceLevel = read i }
    uhcFlagsFlag s o      = return $ o { optUHCFlags = optUHCFlags o ++ [s] }

--- Top-level compilation ---

uhcPreCompile :: UHCOptions -> TCM UHCOptions
uhcPreCompile opts = do
  when (not uhcBackendEnabled) $ typeError $ GenericError "Agda has been built without UHC support. To use the UHC compiler you need to reinstall Agda with 'cabal install Agda -f uhc'."
  -- TODO we should do a version check here at some point.
  let uhc_exist = ExitSuccess
  case uhc_exist of
    ExitSuccess -> do
      copyUHCAgdaBase =<< compileDir
      return opts
    ExitFailure _ -> internalError "Agda cannot find the UHC compiler."

uhcPostCompile :: UHCOptions -> IsMain -> a -> TCM ()
uhcPostCompile opts NotMain _ = runUHCMain opts Nothing
uhcPostCompile opts IsMain _ = do
  i <- curIF
  main <- getMain i
  -- get core name from modInfo
  crMain <- getCoreName1 main
  runUHCMain opts $ Just (iModuleName i, crMain)

--- Module compilation ---

type UHCModuleEnv = ()

uhcPreModule :: UHCOptions -> ModuleName -> FilePath -> TCM (Recompile UHCModuleEnv ())
uhcPreModule _ m ifile = ifM uptodate noComp yesComp
  where
    uptodate = liftIO =<< isNewerThan <$> corePath m <*> pure ifile

    noComp  = return $ Skip ()
    yesComp = return $ Recompile ()

uhcPostModule :: UHCOptions -> UHCModuleEnv -> IsMain -> ModuleName -> a -> TCM ()
uhcPostModule opts _ _ _ _ = compileModule opts =<< curIF


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


-- | Compiles a module and it's imports. Returns the module info
-- of this module, and the accumulating module interface.
compileModule :: UHCOptions -> Interface -> TCM ()
compileModule opts i = do
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
    _ <- writeCoreFile opts crFile code
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

writeCoreFile :: UHCOptions -> String -> UB.CModule -> TCM ()
writeCoreFile opts f cmod = do
  let useTextual = optUHCTextualCore opts

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
    :: UHCOptions
    -> Maybe (ModuleName, HsName)  -- main module
    -> TCM ()
runUHCMain opts mainInfo = do
    otherFps <- mapM (corePath . iModuleName . miInterface) =<< (M.elems <$> getVisitedModules)
    allFps <-
      case mainInfo of
            Nothing -> return otherFps
            Just (mainMod, mainName) -> do
                fp <- (</> "Main.bcr") <$> compileDir
                let mmod = FAgda.createMainModule mainMod mainName
                writeCoreFile opts fp mmod
                return ["Main.bcr"]

    let extraOpts = maybe
            ["--compile-only"]
            ((\x -> [x]) . ("--output="++) . prettyShow . last . mnameToList . fst)
            mainInfo

    liftIO . setCurrentDirectory =<< compileDir

    -- TODO drop the RTS args as soon as we don't need the additional
    -- memory anymore
    callUHC1 opts $
                [ "--pkg-hide-all"
                , "--pkg-expose=uhcbase"
                , "--pkg-expose=base"
                , "UHC/Agda/double.c"
                ] ++ extraOpts ++ allFps ++ ["+RTS", "-K50m", "-RTS"]

callUHC1 :: UHCOptions -> [String] -> TCM ()
callUHC1 opts args = do
    let uhcBin    = getUhcBin opts
        doCall    = optUHCCallUHC opts
        extraArgs = optUHCFlags opts
    callCompiler doCall uhcBin (args ++ extraArgs)

getUhcBin :: UHCOptions -> FilePath
getUhcBin = fromMaybe ("uhc") . optUHCBin
