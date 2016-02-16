
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import Distribution.Simple.BuildPaths (exeExtension)
import Distribution.PackageDescription
import System.FilePath
import System.Process
import System.Exit

main = defaultMainWithHooks hooks

hooks = simpleUserHooks { regHook = checkAgdaPrimitive }

checkAgdaPrimitive :: PackageDescription -> LocalBuildInfo -> UserHooks -> RegisterFlags -> IO ()
checkAgdaPrimitive pkg info hooks flags | regGenPkgConf flags /= NoFlag = return ()   -- Gets run twice, only do this the second time
checkAgdaPrimitive pkg info hooks flags = do
  let dirs = absoluteInstallDirs pkg info NoCopyDest
      agda = buildDir info </> "agda" </> "agda" <.> exeExtension
      prim = datadir dirs </> "lib" </> "prim" </> "Agda" </> "Primitive" <.> "agda"
  putStrLn "Generating Agda library interface files..."
  ok <- rawSystem agda [prim, "-v0"]
  case ok of
    ExitSuccess   -> return ()
    ExitFailure _ -> putStrLn "WARNING: Failed to typecheck Agda.Primitive!"

