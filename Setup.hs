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
import System.Directory (removeFile)
import System.Process
import System.Exit
import System.IO.Error (isDoesNotExistError)

import Control.Exception (catch, throwIO)


main = defaultMainWithHooks hooks

hooks = simpleUserHooks { preConf = notSupportedGHC861
                        , regHook = checkAgdaPrimitiveAndRegister
                        }

builtins :: FilePath -> IO [FilePath]
builtins = find always (extension ==? ".agda")

toIFile :: FilePath -> FilePath
toIFile file = replaceExtension file ".agdai"

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

      removeIfExists file = do
        removeFile file `catch` handleExists
          where handleExists e | isDoesNotExistError e = return ()
                               | otherwise             = throwIO e

      checkPrim file = do
        removeIfExists (toIFile file)
        ok <- rawSystem agda [file, "-v0"]
        case ok of
          ExitSuccess   -> return ()
          ExitFailure _ -> die $ "Error: Failed to typecheck " ++ file ++ "!"

  putStrLn "Generating Agda library interface files..."
  checkPrim prim
  auxPrims <- builtins (auxDir </> "Primitive")
  auxBuiltins <- builtins (auxDir </> "Builtin")
  mapM_ checkPrim (auxPrims ++ auxBuiltins)

checkAgdaPrimitiveAndRegister :: PackageDescription -> LocalBuildInfo -> UserHooks -> RegisterFlags -> IO ()
checkAgdaPrimitiveAndRegister pkg info hooks flags = do
  checkAgdaPrimitive pkg info flags
  regHook simpleUserHooks pkg info hooks flags  -- This actually does something useful

ghcFullVersion :: IO String
ghcFullVersion = filter (/= '\n') <$> readProcess "ghc" [ "--numeric-version" ] []

notSupportedGHC861 :: Args -> ConfigFlags -> IO HookedBuildInfo
notSupportedGHC861 _ _ = do
  ghcVersion <- ghcFullVersion
  if ghcVersion == "8.6.1"
    then die "Error: Agda cannot be built with GHC 8.6.1 due to a compiler bug"
    else (return emptyHookedBuildInfo)
