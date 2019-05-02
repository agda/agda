
------------------------------------------------------------------------
-- | A command which calls a compiler
------------------------------------------------------------------------

module Agda.Compiler.CallCompiler where

import qualified Control.Exception as E
import Control.Monad.Trans

import Data.List ( intercalate )
import qualified Data.List as List
import System.Exit
import System.IO
import System.Process

import Agda.TypeChecking.Monad

import Agda.Utils.Impossible

-- | Calls a compiler:
--
-- * Checks the exit code to see if the compiler exits successfully.
--   If not, then an exception is raised, containing the text the
--   compiler printed to stderr (if any).
--
-- * Uses the debug printout machinery to relay any progress
--   information the compiler prints to stdout.

callCompiler
  :: Bool
     -- ^ Should we actually call the compiler
  -> FilePath
     -- ^ The path to the compiler
  -> [String]
     -- ^ Command-line arguments.
  -> TCM ()
callCompiler doCall cmd args =
  if doCall then do
    merrors <- callCompiler' cmd args
    case merrors of
      Nothing     -> return ()
      Just errors -> typeError (CompilationError errors)
  else
    reportSLn "compile.cmd" 1 $ "NOT calling: " ++ intercalate " " (cmd : args)

-- | Generalisation of @callCompiler@ where the raised exception is
-- returned.
callCompiler'
  :: FilePath
     -- ^ The path to the compiler
  -> [String]
     -- ^ Command-line arguments.
  -> TCM (Maybe String)
callCompiler' cmd args = do
  reportSLn "compile.cmd" 1 $ "Calling: " ++ intercalate " " (cmd : args)
  (_, out, err, p) <-
    liftIO $ createProcess
               (proc cmd args) { std_err = CreatePipe
                               , std_out = CreatePipe
                               }

  -- In -v0 mode we throw away any progress information printed to
  -- stdout.
  case out of
    Nothing  -> __IMPOSSIBLE__
    Just out -> forkTCM $ do
      -- The handle should be in text mode.
      liftIO $ hSetBinaryMode out False
      progressInfo <- liftIO $ hGetContents out
      mapM_ (reportSLn "compile.output" 1) $ lines progressInfo

  errors <- liftIO $ case err of
    Nothing  -> __IMPOSSIBLE__
    Just err -> do
      -- The handle should be in text mode.
      hSetBinaryMode err False
      hGetContents err

  exitcode <- liftIO $ do
    -- Ensure that the output has been read before waiting for the
    -- process.
    _ <- E.evaluate (length errors)
    waitForProcess p

  case exitcode of
    ExitFailure _ -> return $ Just errors
    _             -> return Nothing
