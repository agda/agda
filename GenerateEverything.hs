{-# LANGUAGE PatternGuards #-}

-- This program requires that the filepath and FileManip packages from
-- Hackage are installed.

import qualified Data.List as List
import Control.Applicative
import System.Environment
import System.IO
import System.Exit
import System.FilePath
import System.FilePath.Find

headerFile = "Header"
outputFile = "Everything.agda"
srcDir     = "src"

main = do
  args <- getArgs
  case args of
    [] -> return ()
    _  -> hPutStr stderr usage >> exitFailure

  header  <- readFile headerFile
  modules <- filter isLibraryModule . List.sort <$>
               find always
                    (extension ~~? ".agda" ||? extension ~~? ".lagda")
                    srcDir
  headers <- mapM extractHeader modules

  writeFile outputFile $
    header ++ format (zip modules headers)

-- | Usage info.

usage :: String
usage = unlines
  [ "Usage: runhaskell GenerateEverything.hs"
  , ""
  , "This program should be run in the base directory of a clean checkout of"
  , "the library."
  , ""
  , "The program generates documentation for the library by extracting"
  , "headers from library modules. The output is written to " ++ outputFile
  , "with the file " ++ headerFile ++ " inserted verbatim at the beginning."
  ]

-- | Returns 'True' for all Agda files except for core modules.

isLibraryModule :: FilePath -> Bool
isLibraryModule f =
  takeExtension f `elem` [".agda", ".lagda"] &&
  dropExtension (takeFileName f) /= "Core"

-- | Reads a module and extracts the header.

extractHeader :: FilePath -> IO [String]
extractHeader mod = fmap (extract . lines) $ readFile mod
  where
  delimiter = all (== '-')

  extract (d1 : ss)
    | delimiter d1
    , (info, d2 : rest) <- span ("-- " `List.isPrefixOf`) ss
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
-- assumed that the file name corresponds to an Agda module under
-- 'srcDir'.

fileToMod :: FilePath -> String
fileToMod = map slashToDot . dropExtension . makeRelative srcDir
  where
  slashToDot c | isPathSeparator c = '.'
               | otherwise         = c
