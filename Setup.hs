
import Data.List
import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import Distribution.Simple.BuildPaths (exeExtension)
import Distribution.PackageDescription
import System.FilePath
import System.Process
import System.Exit
import System.Directory
import Data.Version
import Control.Exception
import Data.List

main = defaultMainWithHooks hooks

hooks = simpleUserHooks { regHook = checkAgdaPrimitiveAndRegister }

checkAgdaPrimitive :: PackageDescription -> LocalBuildInfo -> RegisterFlags -> IO ()
checkAgdaPrimitive pkg info flags | regGenPkgConf flags /= NoFlag = return ()   -- Gets run twice, only do this the second time
checkAgdaPrimitive pkg info flags = do
  let dirs = absoluteInstallDirs pkg info NoCopyDest
      prim = datadir dirs </> "prim"
      builtins = datadir dirs </> "builtins"
      version = pkgVersion $ package pkg
      pkgDir = datadir dirs </> showVersion version </> "packages"

  agdaPkg <- makeAbsolute $ buildDir info </> "agda-pkg" </> "agda-pkg" <.> exeExtension

  pkgDirExists <- doesDirectoryExist pkgDir
  if pkgDirExists
    then do
      putStrLn $ "Removing old Agda package db (" ++ pkgDir ++ ") ..."
      removeDirectoryRecursive pkgDir
    else return ()

  putStrLn $ "Setting up Agda default package DB ..."
  putStrLn $ "Using agda-pkg: " ++ agdaPkg

  callProcess agdaPkg ["init-pkg-db", pkgDir]

  putStrLn "Installing Agda-Primitives package ..."

  let installArgs = ["install", "--no-cabal-package", "--agda-package-db=__GLOBAL_DB__"
                    , "--temp-build-dir"]
  callProcess' prim agdaPkg installArgs
  callProcess' builtins agdaPkg installArgs


callProcess' :: FilePath -> FilePath -> [String] -> IO ()
callProcess' wd exe args = do
  (_, _, _, p) <- createProcess $ (proc exe args) { cwd = Just wd }
  r <- waitForProcess p
  case r of
    ExitSuccess   -> return ()
    ExitFailure _ -> do
      putStrLn "WARNING: Failed to typecheck Agda.Primitive!"
      exitWith $ ExitFailure (-1)


checkAgdaPrimitiveAndRegister :: PackageDescription -> LocalBuildInfo -> UserHooks -> RegisterFlags -> IO ()
checkAgdaPrimitiveAndRegister pkg info hooks flags = do
  checkAgdaPrimitive pkg info flags
  regHook simpleUserHooks pkg info hooks flags  -- This actually does something useful
