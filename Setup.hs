{-# LANGUAGE ScopedTypeVariables #-}

import Data.List
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

import Control.Monad
import Control.Exception

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
  pd' = pd { dataFiles = concatMap (expandAgdaExt pd) $ dataFiles pd }

-- Andreas, 2020-04-25, issue #4569: defer 'generateInterface' until after
-- the library has been copied to a destination where it can be found.
-- @cabal build@ will likely no longer produce the .agdai files, but @cabal install@ does.
copyHook' :: PackageDescription -> LocalBuildInfo -> UserHooks -> CopyFlags -> IO ()
copyHook' pd lbi hooks flags = do
  -- Copy library and executable etc.
  copyHook simpleUserHooks pd lbi hooks flags
  unless (skipInterfaces lbi) $ do
    -- Generate .agdai files.
    success <- generateInterfaces pd lbi
    -- Copy again, now including the .agdai files.
    when success $ copyHook simpleUserHooks pd' lbi hooks flags
  where
  pd' = pd
    { dataFiles = concatMap (expandAgdaExt pd) $ dataFiles pd
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
expandAgdaExt :: PackageDescription -> FilePath -> [FilePath]
expandAgdaExt pd fp | takeExtension fp == ".agda" = [ fp, toIFile pd fp ]
                    | otherwise                   = [ fp ]

version :: PackageDescription -> String
version = intercalate "." . map show . versionNumbers . pkgVersion . package

projectRoot :: PackageDescription -> FilePath
projectRoot pd = takeDirectory agdaLibFile where
  [agdaLibFile] = filter ((".agda-lib" ==) . takeExtension) $ dataFiles pd

toIFile :: PackageDescription -> FilePath -> FilePath
toIFile pd file = buildDir </> fileName where
  root = projectRoot pd
  buildDir = root </> "_build" </> version pd </> "agda"
  fileName = makeRelative root $ replaceExtension file ".agdai"

-- Andreas, 2019-10-21, issue #4151:
-- skip the generation of interface files with program suffix "-quicker"
skipInterfaces :: LocalBuildInfo -> Bool
skipInterfaces lbi = fromPathTemplate (progSuffix lbi) == "-quicker"

-- | Returns 'True' if call to Agda executes without error.
--
generateInterfaces :: PackageDescription -> LocalBuildInfo -> IO Bool
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
    let fullpathi = toIFile pd (ddir </> fp)

        handleExists e | isDoesNotExistError e = return ()
                       | otherwise             = throwIO e

    removeFile fullpathi `catch` handleExists

  -- Type-check all builtin modules (in a single Agda session to take
  -- advantage of caching).
  let agdaDirEnvVar = "Agda_datadir"
  let agdaArgs =
        [ "--interaction"
        , "--interaction-exit-on-error"
        , "-Werror"
        , "-v0"
        ]
  let loadBuiltinCmds =
        [ cmd ("Cmd_load_no_metas " ++ f)
            -- Fail if any meta-variable is unsolved.
        | b <- builtins
        , let f     = show (ddir </> b)
              cmd c = "IOTCM " ++ f ++ " None Indirect (" ++ c ++ ")"
        ]
  let callLines = concat
        [ [ unwords $ concat
            [ [ concat [ agdaDirEnvVar, "=", ddir ] ]
            , [ agda ]
            , agdaArgs
            , [ "<<EOF" ]
            ]
          ]
        , loadBuiltinCmds
        , [ "EOF" ]
        ]
  let onIOError (e :: IOException) = False <$ do
        putStr $ unlines $ concat
          [ [ "*** Warning!"
            , "*** Could not generate Agda library interface files."
            , "*** Reason:"
            , show e
            , "*** The attempted call to Agda was:"
            ]
          , callLines
          , [ "*** Ignoring error, continuing installation..." ]
          ]
  env <- getEnvironment
  handle onIOError $ do
    True <$ readCreateProcess
      (proc agda agdaArgs)
        { delegate_ctlc = True
                          -- Make Agda look for data files in a
                          -- certain place.
        , env           = Just ((agdaDirEnvVar, ddir) : env)
        }
      (unlines loadBuiltinCmds)


agdaExeExtension :: String
agdaExeExtension = exeExtension buildPlatform
