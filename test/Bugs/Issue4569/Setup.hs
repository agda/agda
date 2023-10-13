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
import System.IO.Error (isDoesNotExistError)

import Control.Monad (when, forM_, unless)
import Control.Exception (catch, throwIO)

main :: IO ()
main = defaultMainWithHooks userhooks

userhooks :: UserHooks
userhooks = simpleUserHooks { buildHook = buildHook' }

buildHook' :: PackageDescription -> LocalBuildInfo -> UserHooks -> BuildFlags -> IO ()
buildHook' pd lbi hooks flags = do

  -- for debugging, this is examples how you can inspect the flags...
  -- print $ flagAssignment lbi
  -- print $ fromPathTemplate $ progSuffix lbi

  -- build first
  buildHook simpleUserHooks pd lbi hooks flags

  -- then...
  let bdir  = buildDir lbi
      hello = bdir </> "hello-world" </> "hello-world" <.> helloExeExtension
      args  = []

  putStrLn $ "Running hello from installer..."
  (_,_,_,p) <- createProcess_ "rawSystem" (proc hello args) { delegate_ctlc = True }
  ok <- waitForProcess p

  case ok of
    ExitSuccess   -> return ()
    ExitFailure _ -> die $ "Error: failed to run hello from installer"

helloExeExtension :: String
helloExeExtension = exeExtension buildPlatform
