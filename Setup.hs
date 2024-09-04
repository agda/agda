{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Data.Functor ( (<&>) )
import Data.List    ( intercalate )
import Data.Maybe   ( catMaybes )

import Distribution.Simple
import Distribution.Simple.LocalBuildInfo
import Distribution.Simple.Setup
import Distribution.Simple.BuildPaths (exeExtension)
import Distribution.PackageDescription
import Distribution.System ( buildPlatform )

import System.FilePath
import System.Directory (doesFileExist, makeAbsolute, removeFile)
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
  if wantInterfaces flags && not (skipInterfaces lbi) then do
    -- Generate .agdai files.
    success <- generateInterfaces pd lbi
    -- Copy again, now including the .agdai files.
    when success $ copyHook simpleUserHooks pd' lbi hooks flags
  else
    putStrLn "Skipping generation of Agda core library interface files"
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

-- We only want to write interfaces if installing the executable.
-- If we're installing *just* the library, the interface files are not needed
-- and, most importantly, the executable will not be available to be run (cabal#10235)
wantInterfaces :: CopyFlags -> Bool
wantInterfaces _flags = do
#if MIN_VERSION_Cabal(3,11,0)
    any isAgdaExe (copyArgs _flags)
      where
        isAgdaExe "exe:agda" = True
        isAgdaExe _ = False
#else
  True
#endif

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

  putStrLn "Generating Agda core library interface files..."

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
        warn $ concat
          [ [ "*** Could not generate Agda library interface files."
            , "*** Reason:"
            , show e
            , "*** The attempted call to Agda was:"
            ]
          , callLines
          ]
  env <- getEnvironment
  handle onIOError $ do

    -- Generate interface files via a call to Agda.
    readCreateProcess
      (proc agda agdaArgs)
        { delegate_ctlc = True
                          -- Make Agda look for data files in a
                          -- certain place.
        , env           = Just ((agdaDirEnvVar, ddir) : env)
        }
      (unlines loadBuiltinCmds)

    -- Check whether all interface files have been generated.
    missing <- catMaybes <$> forM interfaces \ f ->
      doesFileExist f <&> \case
        True  -> Nothing
        False -> Just f

    -- Warn if not all interface files have been generated, but don't crash.
    -- This might help with issue #7455.
    let success = null missing
    unless success $ warn $ concat
      [ [ "*** Agda failed to generate the following library interface files:" ]
      , missing
      ]
    return success

warn :: [String] -> IO ()
warn msgs = putStr $ unlines $ concat
    [ [ "*** Warning!" ]
    , msgs
    , [ "*** Ignoring error, continuing installation..." ]
    ]



agdaExeExtension :: String
agdaExeExtension = exeExtension buildPlatform
