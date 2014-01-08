
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import Distribution.Simple.BuildPaths (exeExtension)
import Distribution.PackageDescription
import System.FilePath
import System.Process
import System.Exit

main = defaultMainWithHooks hooks

hooks = simpleUserHooks { postInst = checkAgdaPrimitive }

checkAgdaPrimitive :: Args -> InstallFlags -> PackageDescription -> LocalBuildInfo -> IO ()
checkAgdaPrimitive args flags pkg info = do
  let dirs = absoluteInstallDirs pkg info NoCopyDest
      agda = buildDir info </> "Agda/agda" <.> exeExtension
      prim = datadir dirs </> "lib/prim/Agda/Primitive.agda"
  putStrLn "Generating Agda library interface files..."
  ok <- system $ agda ++ " " ++ prim ++ " -v0"
  case ok of
    ExitSuccess   -> return ()
    ExitFailure _ -> putStrLn "WARNING: Failed to typecheck Agda.Primitive!"

