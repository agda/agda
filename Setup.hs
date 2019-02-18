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
import System.Directory (makeAbsolute, removeFile)
import System.Environment (getEnvironment)
import System.Process
import System.Exit
import System.IO.Error (isDoesNotExistError)

import Control.Monad (when, forM_)
import Control.Exception (catch, throwIO)

main :: IO ()
main = defaultMainWithHooks userhooks

userhooks :: UserHooks
userhooks = simpleUserHooks { buildHook = buildHook'
                            , copyHook  = copyHook'
                            , instHook  = instHook'
                            }

-- Install and copy hooks are default, but amended with .agdai files in data-files.
instHook' :: PackageDescription -> LocalBuildInfo -> UserHooks -> InstallFlags -> IO ()
instHook' pd lbi hooks flags = instHook simpleUserHooks pd' lbi hooks flags where
  pd' = pd { dataFiles = concatMap expandAgdaExt $ dataFiles pd }

copyHook' :: PackageDescription -> LocalBuildInfo -> UserHooks -> CopyFlags -> IO ()
copyHook' pd lbi hooks flags = copyHook simpleUserHooks pd' lbi hooks flags where
  pd' = pd { dataFiles = concatMap expandAgdaExt $ dataFiles pd }

-- Used to add .agdai files to data-files
expandAgdaExt :: FilePath -> [FilePath]
expandAgdaExt fp | takeExtension fp == ".agda" = [ fp, toIFile fp ]
                 | otherwise                   = [ fp ]

toIFile :: FilePath -> FilePath
toIFile file = replaceExtension file ".agdai"

buildHook' :: PackageDescription -> LocalBuildInfo -> UserHooks -> BuildFlags -> IO ()
buildHook' pd lbi hooks flags = do
  -- build first
  buildHook simpleUserHooks pd lbi hooks flags

  -- then...
  let bdir = buildDir lbi
      agda = bdir </> "agda" </> "agda" <.> agdaExeExtension

  ddir <- makeAbsolute $ "src" </> "data"

  -- assuming we want to type check all .agda files in data-files
  -- current directory root of the package.

  putStrLn "Generating Agda library interface files..."
  forM_ (dataFiles pd) $ \fp -> when (takeExtension fp == ".agda") $ do
    let fullpath  = ddir </> fp
    let fullpathi = toIFile fullpath

    -- remove existing interface file
    let handleExists e | isDoesNotExistError e = return ()
                       | otherwise             = throwIO e

    removeFile fullpathi `catch` handleExists

    putStrLn $ "... " ++ fullpath
    ok <- rawSystem' ddir agda [ fullpath, "-v0" ]
    case ok of
      ExitSuccess   -> return ()
      ExitFailure _ -> die $ "Error: Failed to typecheck " ++ fullpath ++ "!"

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

rawSystem' :: FilePath -> String -> [String] -> IO ExitCode
rawSystem' agda_datadir cmd args = do
  -- modify environment with Agda_datadir, so agda-executable will look
  -- for data-files in the right place
  e <- getEnvironment
  let e' = ("Agda_datadir", agda_datadir) : e
  (_,_,_,p) <- createProcess_ "rawSystem" (proc cmd args) { delegate_ctlc = True, env = Just e' }
  waitForProcess p
