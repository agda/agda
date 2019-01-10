{-# LANGUAGE CPP #-}

import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import Distribution.Simple.BuildPaths (exeExtension)
import Distribution.PackageDescription
-- ASR (2019-01-10): The Cabal macro @MIN_VERSION_Cabal@ is avaliable
-- from Cabal_>_1.24 so this macro is not supported with the
-- "standard" GHC 7.10.3 which is shipped with Cabal 1.22.5.0.
#if __GLASGOW_HASKELL__ > 710
#if MIN_VERSION_Cabal(2,3,0)
import Distribution.System ( buildPlatform )
#endif
#endif
import System.FilePath
import System.FilePath.Find
import System.Process
import System.Exit


main = defaultMainWithHooks hooks

hooks = simpleUserHooks { regHook = checkAgdaPrimitiveAndRegister }

builtins :: FilePath -> IO [FilePath]
builtins = find always (extension ==? ".agda")

agdaExeExtension :: String
-- ASR (2019-01-10): The Cabal macro @MIN_VERSION_Cabal@ is avaliable
-- from Cabal_>_1.24 so this macro is not supported with the
-- "standard" GHC 7.10.3 which is shipped with Cabal 1.22.5.0.
#if __GLASGOW_HASKELL__ > 710
#if MIN_VERSION_Cabal(2,3,0)
agdaExeExtension = exeExtension buildPlatform
#else
agdaExeExtension = exeExtension
#endif
#else
agdaExeExtension = exeExtension
#endif

checkAgdaPrimitive :: PackageDescription -> LocalBuildInfo -> RegisterFlags -> IO ()
-- ASR (2019-01-10): This fun run twice using Cabal < 2.0.0.0. It is
-- getting difficult to continue supporting GHC 7.10.3! See issues
-- #3128 and #3444.
--
-- Hack! I'm supposing the user on GHC 7.10.3 is using
-- Cabal < 2.0.0.0. Note that GHC 7.10.3 is shipped with
-- Cabal 1.22.5.0.
#if __GLASGOW_HASKELL__ == 710
checkAgdaPrimitive pkg info flags | regGenPkgConf flags /= NoFlag = return ()   -- Gets run twice, only do this the second time
#endif

#if __GLASGOW_HASKELL__ > 710
#if !MIN_VERSION_Cabal(2,0,0)
checkAgdaPrimitive pkg info flags | regGenPkgConf flags /= NoFlag = return ()   -- Gets run twice, only do this the second time
#endif
#endif
checkAgdaPrimitive pkg info flags = do
  let dirs   = absoluteInstallDirs pkg info NoCopyDest
      agda   = buildDir info </> "agda" </> "agda" <.> agdaExeExtension
      auxDir = datadir dirs </> "lib" </> "prim" </> "Agda"
      prim   = auxDir </> "Primitive" <.> "agda"

      checkPrim file = do
        ok <- rawSystem agda [file, "-v0"]
        case ok of
          ExitSuccess   -> return ()
          ExitFailure _ -> die $ "Error: Failed to typecheck " ++ file ++ "!"

  putStrLn "Generating Agda library interface files..."
  checkPrim prim
  auxBuiltins <- builtins (auxDir </> "Builtin")
  mapM_ checkPrim auxBuiltins

checkAgdaPrimitiveAndRegister :: PackageDescription -> LocalBuildInfo -> UserHooks -> RegisterFlags -> IO ()
checkAgdaPrimitiveAndRegister pkg info hooks flags = do
  checkAgdaPrimitive pkg info flags
  regHook simpleUserHooks pkg info hooks flags  -- This actually does something useful
