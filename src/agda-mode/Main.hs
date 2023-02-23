{-# LANGUAGE ScopedTypeVariables #-}

-- | A program which either tries to add setup code for Agda's Emacs
-- mode to the users .emacs file, or provides information to Emacs
-- about where the Emacs mode is installed.

module Main (main) where

import Control.Exception as E
import Control.Monad
import Data.Char
import Data.List (intercalate, isInfixOf)
import Data.Maybe
import Data.Version
import Numeric
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO
-- import System.IO.Error (isDoesNotExistError)
import System.Process

import Paths_Agda (getDataDir, version)

-- | The program.

main :: IO ()
main = do
  prog <- getProgName
  args <- getArgs
  case args of
    [arg] | arg == locateFlag -> printEmacsModeFile
          | arg == setupFlag  -> do
             dotEmacs <- findDotEmacs
             setupDotEmacs (Files { thisProgram = prog
                                  , dotEmacs    = dotEmacs
                                  })
          | arg == compileFlag ->
             compileElispFiles
    _  -> do inform usage
             exitFailure

-- Command line options.

setupFlag   = "setup"
locateFlag  = "locate"
compileFlag = "compile"

-- | Usage information.

usage :: String
usage = unlines
  [ "This program, which is part of Agda version " ++ ver ++ ", can be run"
  , "in three modes, depending on which option it is invoked with:"
  , ""
  , setupFlag
  , ""
  , "  The program tries to add setup code for Agda's Emacs mode to the"
  , "  current user's .emacs file. It is assumed that the .emacs file"
  , "  uses the character encoding specified by the locale."
  , ""
  , locateFlag
  , ""
  , "  The path to the Emacs mode's main file is printed on standard"
  , "  output (using the UTF-8 character encoding and no trailing"
  , "  newline)."
  , ""
  , compileFlag
  , ""
  , "  The program tries to compile Agda's Emacs mode's source files."
  , ""
  , "  WARNING: If you reinstall the Agda mode without recompiling the Emacs"
  , "  Lisp files, then Emacs may continue using the old, compiled files."
  ]

-- | The current version of Agda.

ver :: String
ver = intercalate "." $ map show $
        versionBranch version

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

data Files = Files { dotEmacs :: FilePath
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
      evaluate (length result)
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
     -- when (isDoesNotExistError e) $ do
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

-- | The Agda mode's Emacs Lisp files, given in the order in which
-- they should be compiled.

emacsLispFiles :: [FilePath]
emacsLispFiles =
  [ "agda2-abbrevs.el"
  , "annotation.el"
  , "agda2-queue.el"
  , "eri.el"
  , "agda2.el"
  , "agda-input.el"
  , "agda2-highlight.el"
  , "agda2-mode.el"
  ]

-- | Tries to compile the Agda mode's Emacs Lisp files.

compileElispFiles :: IO ()
compileElispFiles = do
  dataDir <- (</> "emacs-mode") <$> getDataDir
  let elFiles = map (dataDir </>) emacsLispFiles
  elFiles <- filterM doesFileExist elFiles
  results <- mapM (compile dataDir) elFiles
  case catMaybes results of
    [] -> return ()
    fs -> do
      informLn "Unable to compile the following Emacs Lisp files:"
      mapM_ (informLn . ("  " ++)) fs
      exitFailure
  where
  compile dataDir f = do
    exit <- rawSystemWithDiagnostics "emacs" $
      [ "--quick"                -- 'quick' implies 'no-site-file'
      , "--directory", dataDir
      , "--batch"                -- 'batch' implies 'no-init-file' but not 'no-site-file'.
      , "--eval"
      , "(progn \
           \(setq debug-on-error t) \
           \(setq byte-compile-error-on-warn t) \
           \(batch-byte-compile))"
      , f
      ]
    return $ if exit == ExitSuccess then Nothing else Just f

------------------------------------------------------------------------
-- Helper functions

-- These functions inform the user about something by printing on
-- stderr.

inform   = hPutStr   stderr
informLn = hPutStrLn stderr

parens :: String -> String
parens s = concat [ "(", s, ")" ]

-- LISP application
apply :: [String] -> String
apply = parens . unwords
