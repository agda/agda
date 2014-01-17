-- | This module extracts all the non-ASCII characters used by the
-- library code (along with how many times they are used).

module Main where

import qualified Data.List as L
import Data.Char
import Data.Function
import Control.Applicative
import Numeric ( showHex )
import System.FilePath.Find
import System.IO

readUTF8File :: FilePath -> IO String
readUTF8File f = do
  h <- openFile f ReadMode
  hSetEncoding h utf8
  hGetContents h

main :: IO ()
main = do
  agdaFiles <- find always
                    (extension ==? ".agda" ||? extension ==? ".lagda")
                    "src"
  nonAsciiChars <-
    filter (not . isAscii) . concat <$> mapM readUTF8File agdaFiles
  let table = reverse $
              L.sortBy (compare `on` snd) $
              map (\cs -> (head cs, length cs)) $
              L.group $ L.sort $ nonAsciiChars

  let codePoint :: Char -> String
      codePoint c = showHex (ord c) ""

      uPlus :: Char -> String
      uPlus c = "(U+" ++ codePoint c ++ ")"

  mapM_ (\(c, count) -> putStrLn (c : " " ++ uPlus c ++ ": " ++ show count))
        table
