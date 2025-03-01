{-# OPTIONS_GHC -Wunused-imports #-}

-- | A program which either tries to add setup code for Agda's Emacs
-- mode to the users .emacs file, or provides information to Emacs
-- about where the Emacs mode is installed.

module Main (main) where

import System.Environment
import System.Exit

import Agda.Setup as Agda (getDataDir, setup)
import Agda.Setup.EmacsMode
import Agda.Version (version)

-- | The program.

main :: IO ()
main = do
  prog <- getProgName
  args <- getArgs
  case args of
    [arg]
      | arg == locateFlag -> printEmacsModeFile

      | arg == setupFlag  -> do

          -- Ensure that Agda has been setup so the Emacs mode is available.
          Agda.setup False

          dotEmacs <- findDotEmacs
          setupDotEmacs (Files { thisProgram = prog
                               , dotEmacs    = dotEmacs
                               })

      | arg == compileFlag -> do

          -- Ensure that Agda has been setup so the Emacs mode is available.
          Agda.setup False

          compileElispFiles

    _  -> do
      dir <- getDataDir
      inform $ usage dir
      exitFailure

-- | Usage information.

usage :: FilePath -> String
usage dataDir = unlines
  [ "This program, which is part of Agda version " ++ version ++ ", can be run"
  , "in three modes, depending on which option it is invoked with:"
  , ""
  , setupFlag
  , ""
  , "  The program unloads Agda's data files, including the Emacs mode,"
  , "  to the following location:"
  , ""
  , "    " ++ dataDir
  , ""
  , "  It then tries to add setup code for Agda's Emacs mode to the"
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
  , "  The program unloads Agda's data files, including the Emacs mode,"
  , "  to the following location:"
  , ""
  , "    " ++ dataDir
  , ""
  , "  It then tries to compile Agda's Emacs mode's source files."
  , ""
  , "  WARNING: If you reinstall the Agda mode without recompiling the Emacs"
  , "  Lisp files, then Emacs may continue using the old, compiled files."
  ]
