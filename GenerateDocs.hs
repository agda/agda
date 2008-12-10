#!/usr/bin/env runhaskell
{-# LANGUAGE PatternGuards #-}

import Data.List
import System.Environment
import System.IO
import System.Exit

-- Configuration.

-- | The base URL of the darcs repository of the library.

baseURL = "http://www.cs.nott.ac.uk/~nad/listings/lib"

main = do
  args <- getArgs
  case args of
    [] -> return ()
    _  -> hPutStrLn stderr usage >> exitFailure
  readme     <- readFile "Header"
  everything <- readFile "Everything.agda"
  let modules = parse everything
  headers <- mapM extractHeader modules
  let hierarchy = format $ zip modules headers
  putStr (readme ++ hierarchy)

-- | Usage info.

usage :: String
usage = unlines
  [ "Usage: GenerateDocs.hs"
  , ""
  , "This program has to be run from the library's base directory."
  , ""
  , "The program generates overall documentation for the library by"
  , "extracting the header of every file listed in Everything.agda and"
  , "generating a page suitable for inclusion in the Agda Wiki. The"
  , "Header file is included verbatim at the top of this page."
  , ""
  , "The output is written to stdout."
  ]

-- | Parses the "Everything.agda" file.

parse :: String -> [String]
parse = map (drop (length imp)) . filter (imp `isPrefixOf`) . lines
  where imp = "import "

-- | Translates a module name to the corresponding file name.

modToFile :: String -> FilePath
modToFile = (++ ".agda") . map toSlash
  where
  toSlash '.' = '/'
  toSlash c   = c

-- | Translates a module name to the corresponding URL.

modToURL :: String -> FilePath
modToURL m = baseURL ++ "/" ++ m ++ ".html"

-- | Reads a module and extracts the header.

extractHeader :: String -> IO String
extractHeader mod = fmap (extract . lines) $ readFile (modToFile mod)
  where
  delimiter = all (== '-')

  extract (d1 : ss)
    | delimiter d1
    , (info, d2 : rest) <- span ("-- " `isPrefixOf`) ss
    , delimiter d2
    = unlines $ map (drop 3) info
  extract _ = error $ mod ++ " is malformed."

-- | Formats the extracted module information.

format :: [( String -- ^ Module name.
           , String -- ^ Header.
           )]
       -> String
format = unlines . map fmt
  where
  fmt (mod, header) = ":[[" ++ modToURL mod ++ "|" ++ mod ++ "]]: "
                      ++ simplify header
    where simplify = unwords . words
