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
expandAgdaExt pd = \ fp ->
    -- N.B. using lambda here so that @expandAgdaExt pd@ can be partially evaluated.
    if takeExtension fp == ".agda" then [ fp, iFile fp ] else [ fp ]
  where
  iFile = toIFile pd

version :: PackageDescription -> String
version = intercalate "." . map show . versionNumbers . pkgVersion . package

-- | This returns @lib/prim@.
--
projectRoot :: PackageDescription -> FilePath
projectRoot pd = takeDirectory agdaLibFile
  where
  [agdaLibFile] = filter ((".agda-lib" ==) . takeExtension) $ dataFiles pd

-- | Turns e.g. @lib/prim/Agda/Primitive.agda@
--   into @lib/prim/_build/2.7.0/agda/Agda/Primitive.agdai@.
--
--   An absolute path will be returned unchanged.
toIFile ::
     PackageDescription
  -> FilePath            -- ^ Should be a relative path.
  -> FilePath            -- ^ Then this is also a relative path.
toIFile pd = (buildDir </>) . fileName
  where
  root = projectRoot pd
    -- e.g. root     = "lib/prim"
  buildDir = root </> "_build" </> version pd </> "agda"
    -- e.g. buildDir = "lib/prim/_build/2.7.0/agda"
  fileName file = makeRelative root $ replaceExtension file ".agdai"
    -- e.g. fileName "lib/prim/Agda/Primitive.agda" = "Agda/Primitive.agdai"

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

  -- We should be in the current directory root of the cabal package
  -- and data-files reside in src/data relative to this.
  --
  ddir <- makeAbsolute $ "src" </> "data"

  putStrLn "Generating Agda library interface files..."

  -- The Agda.Primitive* and Agda.Builtin* modules.
  let builtins = filter ((== ".agda") . takeExtension) (dataFiles pd)

  -- The absolute filenames of their interfaces.
  let interfaces = map ((ddir </>) . toIFile pd) builtins

  -- Remove all existing .agdai files.
  forM_ interfaces $ \ fp -> removeFile fp `catch` \ e ->
    unless (isDoesNotExistError e) $ throwIO e

  -- Type-check all builtin modules (in a single Agda session to take
  -- advantage of caching).
  let agdaDirEnvVar = "Agda_datadir"
  let agdaArgs =
        [ "--interaction"
        , "--interaction-exit-on-error"
        , "-Werror"
        , "-v0"
        ]
  let loadBuiltinCmds = concat
        [ [ cmd ("Cmd_load " ++ f ++ " []")
          , cmd "Cmd_no_metas"
            -- Fail if any meta-variable is unsolved.
          ]
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
