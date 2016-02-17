
import Data.List
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import Distribution.Simple.BuildPaths (exeExtension)
import Distribution.PackageDescription
import System.FilePath
import System.Process
import System.Exit

main = defaultMainWithHooks hooks

hooks = simpleUserHooks { regHook = checkAgdaPrimitiveAndRegister }

builtins :: [String]
builtins =
  [ "Bool", "Char", "Coinduction", "Equality", "Float"
  , "FromNat", "FromNeg", "FromString", "IO", "Int", "List"
  , "Nat", "Reflection", "Size", "Strict", "String"
  , "TrustMe", "Unit" ]

checkAgdaPrimitive :: PackageDescription -> LocalBuildInfo -> RegisterFlags -> IO ()
checkAgdaPrimitive pkg info flags | regGenPkgConf flags /= NoFlag = return ()   -- Gets run twice, only do this the second time
checkAgdaPrimitive pkg info flags = do
  let dirs = absoluteInstallDirs pkg info NoCopyDest
      agda = buildDir info </> "agda" </> "agda" <.> exeExtension
      primMod ms = (ms, datadir dirs </> "lib" </> "prim" </> "Agda" </> foldr1 (</>) ms <.> "agda")
      prims      = primMod ["Primitive"] : [ primMod ["Builtin", m] | m <- builtins ]

      checkPrim (ms, file) = do
        ok <- rawSystem agda [file, "-v0"]
        case ok of
          ExitSuccess   -> return ()
          ExitFailure _ -> putStrLn $ "WARNING: Failed to typecheck " ++ intercalate "." ("Agda" : ms) ++ "!"

  putStrLn "Generating Agda library interface files..."
  mapM_ checkPrim prims

checkAgdaPrimitiveAndRegister :: PackageDescription -> LocalBuildInfo -> UserHooks -> RegisterFlags -> IO ()
checkAgdaPrimitiveAndRegister pkg info hooks flags = do
  checkAgdaPrimitive pkg info flags
  regHook simpleUserHooks pkg info hooks flags  -- This actually does something useful

