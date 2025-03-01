-- {-# OPTIONS_GHC -Wunused-imports #-}

-- | Setup up the emacs mode for Agda.

module Agda.Setup.EmacsMode
  ( help
  -- * Locate
  , locateFlag
  , printEmacsModeFile
  -- * Setup
  , setupFlag
  , setupDotEmacs
  -- * Compile
  , compileFlag
  , compileElispFiles
  -- * Utilities
  , inform
  )
where

import Control.Applicative    ( liftA2 )
import Control.Exception as E ( bracket, catch, evaluate, IOException )
import Control.Monad          ( unless )

import Data.Bifunctor         ( first, second )
import Data.Bool              ( bool )
import Data.Char              ( isAscii, isPrint )
import Data.Functor           ( (<&>) )
import Data.List              ( isInfixOf )
import Data.Maybe             ( catMaybes, fromMaybe )

import Numeric                ( showHex )

import System.Directory       ( doesFileExist, findExecutable, getTemporaryDirectory, removeFile )
import System.Exit            ( exitFailure, ExitCode(ExitSuccess) )
import System.FilePath        ( (</>), getSearchPath )
import System.IO              ( IOMode(ReadMode)
                              , hClose, hSetEncoding, hGetContents, hPutStr, hPutStrLn
                              , openTempFile, stderr, stdout, utf8, withFile
                              )
import System.Process         ( rawSystem, showCommandForUser )

import Agda.Setup             ( getDataDir )
import Agda.Setup.DataFiles   ( emacsLispFiles, emacsModeDir )

-- Command line options.

setupFlag :: String
setupFlag   = "setup"

locateFlag :: String
locateFlag  = "locate"

compileFlag :: String
compileFlag = "compile"

-- | Help topic for @--emacs-mode@.

help :: String
help = unlines
  [ "Option --emacs-mode allows to administer the Agda Emacs mode."
  , "It accepts three commands:"
  , ""
  , setupFlag
  , ""
  , "  This command unpacks Agda's data files, including the Emacs mode,"
  , "  into Agda's data directory (see option --print-agda-data-dir)."
  , ""
  , "  It then tries to add setup code for Agda's Emacs mode to the"
  , "  current user's .emacs file. It is assumed that the .emacs file"
  , "  uses the character encoding specified by the locale."
  , ""
  , compileFlag
  , ""
  , "  This command unpacks Agda's data files, including the Emacs mode,"
  , "  into Agda's data directory."
  , ""
  , "  It then tries to compile Agda's Emacs mode's source files."
  , ""
  , "  WARNING: If you reinstall the Agda mode without recompiling the Emacs"
  , "  Lisp files, then Emacs may continue using the old, compiled files."
  , ""
  , locateFlag
  , ""
  , "  The path to the Emacs mode's main file is printed on standard"
  , "  output (using the UTF-8 character encoding and no trailing"
  , "  newline)."
  ]

------------------------------------------------------------------------
-- Locating the Agda mode

-- | Prints out the path to the Agda mode's main file (using UTF-8 and
-- without any trailing newline).

printEmacsModeFile :: IO ()
printEmacsModeFile = do
  dataDir <- getDataDir
  let path = dataDir </> emacsModeDir </> "agda2.el"
  hSetEncoding stdout utf8
  putStr path

------------------------------------------------------------------------
-- Setting up the .emacs file

-- | Tries to set up the Agda mode in the given .emacs file.

setupDotEmacs :: String -> IO ()
setupDotEmacs agda = do
  let cmd   = agda ++ " --emacs-mode"
  let elisp = setupString cmd

  dotEmacs <- findDotEmacs
  informLn $ "The .emacs file used: " ++ dotEmacs

  alreadyInstalled cmd dotEmacs >>= \case
    True  -> do
      informLn "It seems as if setup has already been performed."
    False -> do
      appendFile dotEmacs elisp
      inform $ unlines $
        [ "Setup done. Try to (re)start Emacs and open an Agda file."
        , "The following text was appended to the .emacs file:"
        ] ++ lines elisp

-- | Tries to find the user's .emacs file by querying Emacs.

findDotEmacs :: IO FilePath
findDotEmacs = askEmacs "(expand-file-name user-init-file)"

-- | Has the Agda mode already been set up?

alreadyInstalled :: String -> FilePath -> IO Bool
alreadyInstalled cmd dotEmacs = do
  doesFileExist dotEmacs >>= \case
    False -> return False
    True  -> withFile dotEmacs ReadMode \ f -> do
      txt <- hGetContents f
      evaluate $ identifier cmd `isInfixOf` txt
        -- Uses evaluate to ensure that the file is not closed prematurely.

-- | If this string occurs in the .emacs file, then it is assumed that
-- setup has already been performed.

identifier :: String -> String
identifier cmd = cmd ++ " " ++ locateFlag

-- | The string appended to the end of the .emacs file.

setupString :: String -> String
setupString cmd = unlines
  [ ""
  , "(load-file (let ((coding-system-for-read 'utf-8))"
  , "                (shell-command-to-string \""
                        ++ identifier cmd ++ "\")))"
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
          (removeFile . fst) $ \ (file, h) -> do
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
    unless (exit == ExitSuccess) do
      informLn "Unable to query Emacs."
      exitFailure
    withFile file ReadMode \ h -> do
      result <- hGetContents h
      _ <- evaluate (length result)
        -- Uses evaluate to ensure that the file is not closed prematurely.
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
  dataDir <- getDataDir <&> (</> emacsModeDir)
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
