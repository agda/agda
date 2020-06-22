{-# LANGUAGE CPP #-}
{-# LANGUAGE NondecreasingIndentation #-}

import Data.Maybe

import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import Distribution.Simple.BuildPaths (exeExtension)
import Distribution.PackageDescription
#if MIN_VERSION_Cabal(2,3,0)
import Distribution.System ( buildPlatform )
#endif
import System.FilePath
import System.Directory (makeAbsolute, removeFile)
import System.Environment (getEnvironment)
import System.Process
import System.Exit
import System.IO.Error (isDoesNotExistError)

import Control.Monad (when, forM_, unless)
import Control.Exception (catch, throwIO)

main :: IO ()
main = defaultMainWithHooks userhooks

userhooks :: UserHooks
userhooks = simpleUserHooks
  { copyHook  = copyHook'
  , instHook  = instHook'
  }

-- Install and copy hooks are default, but amended with .agdai files in data-files.
instHook' :: PackageDescription -> LocalBuildInfo -> UserHooks -> InstallFlags -> IO ()
instHook' pd lbi hooks flags = instHook simpleUserHooks pd' lbi hooks flags where
  pd' = pd { dataFiles = concatMap expandAgdaExt $ dataFiles pd }

-- Andreas, 2020-04-25, issue #4569: defer 'generateInterface' until after
-- the library has been copied to a destination where it can be found.
-- @cabal build@ will likely no longer produce the .agdai files, but @cabal install@ does.
copyHook' :: PackageDescription -> LocalBuildInfo -> UserHooks -> CopyFlags -> IO ()
copyHook' pd lbi hooks flags = do
  -- Copy library and executable etc.
  copyHook simpleUserHooks pd lbi hooks flags
  -- Generate .agdai files.
  generateInterfaces pd lbi
  -- Copy again, now including the .agdai files.
  copyHook simpleUserHooks pd' lbi hooks flags
  where
  pd' = pd
    { dataFiles = concatMap expandAgdaExt $ dataFiles pd
      -- Andreas, 2020-04-25, issue #4569:
      -- I tried clearing some fields to avoid copying again.
      -- However, cabal does not like me messing with the PackageDescription.
      -- Clearing @library@ or @executables@ leads to internal errors.
      -- Thus, we just copy things again.  Not a terrible problem.
    -- , library       = Nothing
    -- , executables   = []
    -- , subLibraries  = []
    -- , foreignLibs   = []
    -- , testSuites    = []
    -- , benchmarks    = []
    -- , extraSrcFiles = []
    -- , extraTmpFiles = []
    -- , extraDocFiles = []
    }

-- Used to add .agdai files to data-files
expandAgdaExt :: FilePath -> [FilePath]
expandAgdaExt fp | takeExtension fp == ".agda" = [ fp, toIFile fp ]
                 | otherwise                   = [ fp ]

toIFile :: FilePath -> FilePath
toIFile file = replaceExtension file ".agdai"

generateInterfaces :: PackageDescription -> LocalBuildInfo -> IO ()
generateInterfaces pd lbi = do

  -- for debugging, these are examples how you can inspect the flags...
  -- print $ flagAssignment lbi
  -- print $ fromPathTemplate $ progSuffix lbi

  -- Andreas, 2019-10-21, issue #4151:
  -- skip the generation of interface files with program suffix "-quicker"
  unless (fromPathTemplate (progSuffix lbi) == "-quicker") $ do

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
    ok <- rawSystem' ddir agda [ "--no-libraries", "--local-interfaces"
                               , "-Werror"
                               , fullpath, "-v0"
                               ]
    case ok of
      ExitSuccess   -> return ()
      ExitFailure _ -> die $ "Error: Failed to typecheck " ++ fullpath ++ "!"

agdaExeExtension :: String
#if MIN_VERSION_Cabal(2,3,0)
agdaExeExtension = exeExtension buildPlatform
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
