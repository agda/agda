{-# LANGUAGE PatternGuards #-}

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

  header  <- readFileUTF8 headerFile
  modules <- filter isLibraryModule . List.sort <$>
               find always
                    (extension ==? ".agda" ||? extension ==? ".lagda")
                    srcDir
  headers <- mapM extractHeader modules

  writeFileUTF8 outputFile $
    header ++ format (zip modules headers)

-- | Usage info.

usage :: String
usage = unlines
  [ "GenerateEverything: A utility program for Agda's standard library."
  , ""
  , "Usage: GenerateEverything"
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
  takeExtension f `elem` [".agda", ".lagda"]
  && dropExtension (takeFileName f) /= "Core"
  && dropExtension (takeFileName f) /= "index"

-- | Reads a module and extracts the header.

extractHeader :: FilePath -> IO [String]
extractHeader mod = fmap (extract . lines) $ readFileUTF8 mod
  where
  delimiter = all (== '-')

  extract (d1 : "-- The Agda standard library" : "--" : ss)
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

-- | A variant of 'readFile' which uses the 'utf8' encoding.

readFileUTF8 :: FilePath -> IO String
readFileUTF8 f = do
  h <- openFile f ReadMode
  hSetEncoding h utf8
  hGetContents h

-- | A variant of 'writeFile' which uses the 'utf8' encoding.

writeFileUTF8 :: FilePath -> String -> IO ()
writeFileUTF8 f s = withFile f WriteMode $ \h -> do
  hSetEncoding h utf8
  hPutStr h s
