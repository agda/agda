
------------------------------------------------------------------------
-- | A command which calls a compiler
------------------------------------------------------------------------

module Agda.Compiler.CallCompiler where

import qualified Control.Exception as E
import Control.Monad.Trans

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
  -> Maybe FilePath
     -- ^ The working directory that should be used when the compiler
     -- is invoked. The default is the current working directory.
  -> Maybe TextEncoding
     -- ^ Use the given text encoding, if any, when reading the output
     -- from the process (stdout and stderr).
  -> TCM ()
callCompiler doCall cmd args cwd enc =
  if doCall then do
    merrors <- callCompiler' cmd args cwd enc
    case merrors of
      Nothing     -> return ()
      Just errors -> typeError (CompilationError errors)
  else
    reportSLn "compile.cmd" 1 $ "NOT calling: " ++ unwords (cmd : args)

-- | Generalisation of @callCompiler@ where the raised exception is
-- returned.
callCompiler'
  :: FilePath
     -- ^ The path to the compiler
  -> [String]
     -- ^ Command-line arguments.
  -> Maybe FilePath
     -- ^ The working directory that should be used when the compiler
     -- is invoked. The default is the current working directory.
  -> Maybe TextEncoding
     -- ^ Use the given text encoding, if any, when reading the output
     -- from the process (stdout and stderr).
  -> TCM (Maybe String)
callCompiler' cmd args cwd enc = do
  reportSLn "compile.cmd" 1 $ "Calling: " ++ unwords (cmd : args)
  (_, out, err, p) <-
    liftIO $ createProcess
               (proc cmd args) { std_err = CreatePipe
                               , std_out = CreatePipe
                               , cwd     = cwd
                               }

  -- In -v0 mode we throw away any progress information printed to
  -- stdout.
  case out of
    Nothing  -> __IMPOSSIBLE__
    Just out -> forkTCM $ do
      -- The handle should be in text mode.
      liftIO $ hSetBinaryMode out False
      case enc of
        Nothing  -> return ()
        Just enc -> liftIO $ hSetEncoding out enc
      progressInfo <- liftIO $ hGetContents out
      mapM_ (reportSLn "compile.output" 1) $ lines progressInfo

  errors <- liftIO $ case err of
    Nothing  -> __IMPOSSIBLE__
    Just err -> do
      -- The handle should be in text mode.
      hSetBinaryMode err False
      case enc of
        Nothing  -> return ()
        Just enc -> liftIO $ hSetEncoding err enc
      hGetContents err

  exitcode <- liftIO $ do
    -- Ensure that the output has been read before waiting for the
    -- process.
    _ <- E.evaluate (length errors)
    waitForProcess p

  case exitcode of
    ExitFailure _ -> return $ Just errors
    _             -> return Nothing
