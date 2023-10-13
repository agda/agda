{-# LANGUAGE NondecreasingIndentation #-}

import Data.Maybe

import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import Distribution.Simple.BuildPaths (exeExtension)
import Distribution.PackageDescription
import Distribution.System ( buildPlatform )

import System.FilePath
import System.Directory (makeAbsolute, removeFile)
import System.Environment (getEnvironment)
import System.Process
import System.Exit
import System.IO
import System.IO.Error (isDoesNotExistError)

import Control.Monad (forM_, unless)
import Control.Exception (bracket, catch, throwIO)

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
  unless (skipInterfaces lbi) $ do
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

-- Andreas, 2019-10-21, issue #4151:
-- skip the generation of interface files with program suffix "-quicker"
skipInterfaces :: LocalBuildInfo -> Bool
skipInterfaces lbi = fromPathTemplate (progSuffix lbi) == "-quicker"

generateInterfaces :: PackageDescription -> LocalBuildInfo -> IO ()
generateInterfaces pd lbi = do

  -- for debugging, these are examples how you can inspect the flags...
  -- print $ flagAssignment lbi
  -- print $ fromPathTemplate $ progSuffix lbi

  -- then...
  let bdir = buildDir lbi
      agda = bdir </> "agda" </> "agda" <.> agdaExeExtension

  ddir <- makeAbsolute $ "src" </> "data"

  -- assuming we want to type check all .agda files in data-files
  -- current directory root of the package.

  putStrLn "Generating Agda library interface files..."

  -- The Agda.Primitive* and Agda.Builtin* modules.
  let builtins = filter ((== ".agda") . takeExtension) (dataFiles pd)

  -- Remove all existing .agdai files.
  forM_ builtins $ \fp -> do
    let fullpathi = toIFile (ddir </> fp)

        handleExists e | isDoesNotExistError e = return ()
                       | otherwise             = throwIO e

    removeFile fullpathi `catch` handleExists

  -- Type-check all builtin modules (in a single Agda session to take
  -- advantage of caching).
  let loadBuiltinCmds = concat
        [ [ cmd ("Cmd_load " ++ f ++ " []")
          , cmd "Cmd_no_metas"
            -- Fail if any meta-variable is unsolved.
          ]
        | b <- builtins
        , let f     = show (ddir </> b)
              cmd c = "IOTCM " ++ f ++ " None Indirect (" ++ c ++ ")"
        ]
  env <- getEnvironment
  _output <- readCreateProcess
      (proc agda
          [ "--interaction"
          , "--interaction-exit-on-error"
          , "--no-libraries"
          , "--local-interfaces"
          , "-Werror"
          , "-v0"
          ])
        { delegate_ctlc = True
                          -- Make Agda look for data files in a
                          -- certain place.
        , env           = Just (("Agda_datadir", ddir) : env)
        }
      (unlines loadBuiltinCmds)
  return ()

agdaExeExtension :: String
agdaExeExtension = exeExtension buildPlatform
