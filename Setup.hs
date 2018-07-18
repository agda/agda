
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import Distribution.Simple.BuildPaths (exeExtension)
import Distribution.PackageDescription
import System.FilePath
import System.FilePath.Find
import System.Process
import System.Exit

main = defaultMainWithHooks hooks

hooks = simpleUserHooks { regHook = checkAgdaPrimitiveAndRegister }

builtins :: FilePath -> IO [FilePath]
builtins = find always (extension ==? ".agda")

checkAgdaPrimitive :: PackageDescription -> LocalBuildInfo -> RegisterFlags -> IO ()
checkAgdaPrimitive pkg info flags | regGenPkgConf flags /= NoFlag = return ()   -- Gets run twice, only do this the second time
checkAgdaPrimitive pkg info flags = do
  let dirs   = absoluteInstallDirs pkg info NoCopyDest
      agda   = buildDir info </> "agda" </> "agda" <.> exeExtension
      auxDir = datadir dirs </> "lib" </> "prim" </> "Agda"
      prim   = auxDir </> "Primitive" <.> "agda"

      checkPrim file = do
        ok <- rawSystem agda [file, "-v0"]
        case ok of
          ExitSuccess   -> return ()
          ExitFailure _ -> putStrLn $ "WARNING: Failed to typecheck " ++ file ++ "!"

  putStrLn "Generating Agda library interface files..."
  checkPrim prim
  auxBuiltins <- builtins (auxDir </> "Builtins")
  mapM_ checkPrim auxBuiltins

checkAgdaPrimitiveAndRegister :: PackageDescription -> LocalBuildInfo -> UserHooks -> RegisterFlags -> IO ()
checkAgdaPrimitiveAndRegister pkg info hooks flags = do
  checkAgdaPrimitive pkg info flags
  regHook simpleUserHooks pkg info hooks flags  -- This actually does something useful
