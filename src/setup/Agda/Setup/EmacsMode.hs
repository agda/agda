{-# OPTIONS_GHC -Wunused-imports #-}

-- | Setup up the emacs mode for Agda.

module Agda.Setup.EmacsMode
  ( Files(..)
  -- * Locate
  , locateFlag
  , printEmacsModeFile
  -- * Setup
  , setupFlag
  , findDotEmacs
  , setupDotEmacs
  -- * Compile
  , compileElispFiles
  , compileFlag
  -- * Utilities
  , inform
  )
where

import Control.Exception as E
import Control.Monad

import Data.Bifunctor (first, second)
import Data.Bool (bool)
import Data.Char
import Data.List (isInfixOf)
import Data.Maybe

import Numeric

import System.Directory
import System.Exit
import System.FilePath
import System.IO
import System.Process

import Agda.Setup ( getDataDir )
import Agda.Setup.DataFiles ( emacsLispFiles )

-- Command line options.

setupFlag :: String
setupFlag   = "setup"

locateFlag :: String
locateFlag  = "locate"

compileFlag :: String
compileFlag = "compile"

------------------------------------------------------------------------
-- Locating the Agda mode

-- | Prints out the path to the Agda mode's main file (using UTF-8 and
-- without any trailing newline).

printEmacsModeFile :: IO ()
printEmacsModeFile = do
  dataDir <- getDataDir
  let path = dataDir </> "emacs-mode" </> "agda2.el"
  hSetEncoding stdout utf8
  putStr path

------------------------------------------------------------------------
-- Setting up the .emacs file

data Files = Files
  { dotEmacs :: FilePath
      -- ^ The .emacs file.
  , thisProgram :: FilePath
      -- ^ The name of the current program.
  }

-- | Tries to set up the Agda mode in the given .emacs file.

setupDotEmacs :: Files -> IO ()
setupDotEmacs files = do
  informLn $ "The .emacs file used: " ++ dotEmacs files

  already <- alreadyInstalled files
  if already then
    informLn "It seems as if setup has already been performed."
   else do

    appendFile (dotEmacs files) (setupString files)
    inform $ unlines $
      [ "Setup done. Try to (re)start Emacs and open an Agda file."
      , "The following text was appended to the .emacs file:"
      ] ++ lines (setupString files)

-- | Tries to find the user's .emacs file by querying Emacs.

findDotEmacs :: IO FilePath
findDotEmacs = askEmacs "(expand-file-name user-init-file)"

-- | Has the Agda mode already been set up?

alreadyInstalled :: Files -> IO Bool
alreadyInstalled files = do
  exists <- doesFileExist (dotEmacs files)
  if not exists then return False else
    withFile (dotEmacs files) ReadMode $ (evaluate . (identifier files `isInfixOf`)) <=< hGetContents
      -- Uses evaluate to ensure that the file is not closed
      -- prematurely.

-- | If this string occurs in the .emacs file, then it is assumed that
-- setup has already been performed.

identifier :: Files -> String
identifier files =
  takeFileName (thisProgram files) ++ " " ++ locateFlag

-- | The string appended to the end of the .emacs file.

setupString :: Files -> String
setupString files = unlines
  [ ""
  , "(load-file (let ((coding-system-for-read 'utf-8))"
  , "                (shell-command-to-string \""
                        ++ identifier files ++ "\")))"
  ]

------------------------------------------------------------------------
-- Querying Emacs

-- | Evaluates the given Elisp command using Emacs. The output of the
-- command (whatever was written into the current buffer) is returned.
--
-- Note: The input is not checked. The input is assumed to come from a
-- trusted source.

askEmacs :: String -> IO String
askEmacs query = do
  tempDir <- getTemporaryDirectory
  bracket (openTempFile tempDir "askEmacs")
          (removeFile . fst) $ \(file, h) -> do
    hClose h
    exit <- rawSystemWithDiagnostics "emacs"
      [ "--batch"
          -- Andreas, 2022-10-15, issue #5901, suggested by Spencer Baugh (catern):
          -- Use Emacs batch mode so that it can run without a terminal.
      , "--user", ""
          -- The flag --user is necessary with --batch so that user-init-file is defined.
          -- The empty user is the default user.
          -- (Option --batch includes --no-init-file, this is reverted by supplying --user.)
      -- Andreas, 2022-05-25, issue #5901 reloaded:
      -- Loading the init file without loading the site fails for some users:
      -- , "--quick"
      --     -- Option --quick includes --no-site-file.
      , "--eval"
      , apply [ "with-temp-file", escape file, apply [ "insert", query ] ]
          -- Short cutting the temp file via just [ "princ", query ]
          -- does not work if the loading of the user-init-file prints extra stuff.
          -- Going via the temp file we can let this stuff go to stdout without
          -- affecting the output we care about.
      ]
    unless (exit == ExitSuccess) $ do
      informLn "Unable to query Emacs."
      exitFailure
    withFile file ReadMode $ \h -> do
      result <- hGetContents h
      _ <- evaluate (length result)
      -- Uses evaluate to ensure that the file is not closed
      -- prematurely.
      return result

-- | Like 'rawSystem' but handles 'IOException' by printing diagnostics
-- (@PATH@) before 'exitFailure'.

rawSystemWithDiagnostics
  :: FilePath  -- ^ Command to run.
  -> [String]  -- ^ Arguments to command.
  -> IO ExitCode
rawSystemWithDiagnostics cmd args =
    rawSystem cmd args
  `E.catch` \ (e :: IOException) -> do
     informLn $ unwords [ "FAILED:", showCommandForUser cmd args ]
     informLn $ unwords [ "Exception:", show e ]
     -- The PATH might be useful in other exceptions, like "permission denied".
     path <- fromMaybe "(not found)" <$> findExecutable cmd
     informLn $ unwords [ "Executable", cmd, "at:", path ]
     informLn "PATH:"
     mapM_ (informLn . ("  - " ++)) =<< getSearchPath
     exitFailure

-- | Escapes the string so that Emacs can parse it as an Elisp string.

escape :: FilePath -> FilePath
escape s = "\"" ++ concatMap esc s ++ "\""
  where
  esc c | c `elem` ['\\', '"']   = '\\' : [c]
        | isAscii c && isPrint c = [c]
        | otherwise              = "\\x" ++ showHex (fromEnum c) "\\ "

------------------------------------------------------------------------
-- Compiling Emacs Lisp files

-- | Tries to compile the Agda mode's Emacs Lisp files.

compileElispFiles :: IO ()
compileElispFiles = do
  dataDir <- (</> "emacs-mode") <$> getDataDir
  let elFiles = map (dataDir </>) emacsLispFiles
  (existing, missing) <- partitionM doesFileExist elFiles
  failed <- catMaybes <$> mapM (compile dataDir) existing

  -- If any of the .el files was missing or failed to compile, fail execution.
  unless (null missing) $ do
    informLn "Missing Emacs Lisp files:"
    mapM_ (informLn . ("  " ++)) missing
  unless (null failed) $ do
    informLn "Unable to compile the following Emacs Lisp files:"
    mapM_ (informLn . ("  " ++)) failed
  unless (null missing && null failed) exitFailure

  where
  compile dataDir f = do
    exit <- rawSystemWithDiagnostics "emacs" $
      [ "--quick"                -- 'quick' implies 'no-site-file'
      , "--directory", dataDir
      , "--batch"                -- 'batch' implies 'no-init-file' but not 'no-site-file'.
      , "--eval"
      , "(progn \
           \(setq byte-compile-error-on-warn t) \
           \(byte-compile-disable-warning 'cl-functions) \
           \(batch-byte-compile))"
      , f
      ]
    return $ if exit == ExitSuccess then Nothing else Just f

------------------------------------------------------------------------
-- Helper functions

-- These functions inform the user about something by printing on
-- stderr.

inform :: String -> IO ()
inform   = hPutStr   stderr

informLn :: String -> IO ()
informLn = hPutStrLn stderr

parens :: String -> String
parens s = concat [ "(", s, ")" ]

-- LISP application
apply :: [String] -> String
apply = parens . unwords

-- Utilities

-- | A ``monadic'' version of @'partition' :: (a -> Bool) -> [a] -> ([a],[a])
partitionM :: Applicative m => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM f =
  foldr (\ x -> liftA2 (bool (second (x:)) (first (x:))) $ f x)
        (pure ([], []))
