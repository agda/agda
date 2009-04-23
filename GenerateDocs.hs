{-# LANGUAGE PatternGuards #-}

-- This program requires that the filepath and process packages from
-- Hackage are installed.

import Data.List
import System.Environment
import System.IO
import System.Exit
import System.FilePath
import System.Process

headerFile = "Header"
outputFile = "Everything.agda"

main = do
  args <- getArgs
  case args of
    [] -> return ()
    _  -> hPutStr stderr usage >> exitFailure

  header   <- readFile headerFile
  allFiles <- readProcess "darcs" ["show", "files"] ""
  let modules = filter isLibraryModule $ sort $ lines allFiles
  headers <- mapM extractHeader modules

  writeFile outputFile $
    header ++ format (zip modules headers)

-- | Usage info.

usage :: String
usage = unlines
  [ "Usage: runhaskell GenerateDocs.hs"
  , ""
  , "This program has to be run from the library's base directory."
  , ""
  , "The program generates documentation for the library by extracting"
  , "headers from library modules. The output is written to " ++ outputFile
  , "with the file " ++ headerFile ++ " inserted verbatim at the beginning."
  ]

-- | Returns 'True' for all Agda files except for README, Everything
-- and core modules.

isLibraryModule :: FilePath -> Bool
isLibraryModule f =
  takeExtension f `elem` [".agda", ".lagda"]            &&
  dropExtension (takeFileName f) /= "Core"              &&
  not (f `elem` ["./README.agda", "./Everything.agda"])

-- | Reads a module and extracts the header.

extractHeader :: FilePath -> IO [String]
extractHeader mod = fmap (extract . lines) $ readFile mod
  where
  delimiter = all (== '-')

  extract (d1 : ss)
    | delimiter d1
    , (info, d2 : rest) <- span ("-- " `isPrefixOf`) ss
    , delimiter d2
    = info
  extract _ = error $ mod ++ " is malformed."

-- | Formats the extracted module information.

format :: [(FilePath, [String])]
          -- ^ Pairs of module names and headers. All lines in the
          -- headers are already prefixed with \"-- \".
       -> String
format = unlines . concat . map fmt
  where
  fmt (mod, header) = "" : header ++ ["import " ++ fileToMod mod]

-- | Translates a file name to the corresponding module name. It is
-- assumed that the file name corresponds to an Agda module, and that
-- it starts with \"./\".

fileToMod :: FilePath -> String
fileToMod ('.' : '/' : f) = map slashToDot (dropExtension f)
  where
  slashToDot '/' = '.'
  slashToDot c   = c
