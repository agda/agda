-- | This module extracts all the non-ASCII characters used by the
-- library code (along with how many times they are used).
--
-- The implementation relies on the utf8-string and FileManip
-- libraries which are available from Hackage.

module AllNonAsciiChars where

import qualified Data.List as L
import Data.Char
import Data.Function
import Control.Applicative
import System.IO.UTF8 as U
import System.FilePath.Find

main :: IO ()
main = do
  agdaFiles <- find always
                    (extension ~~? ".agda" ||? extension ~~? ".lagda")
                    "src"
  nonAsciiChars <-
    filter (not . isAscii) . concat <$> mapM U.readFile agdaFiles
  let table = reverse $
              L.sortBy (compare `on` snd) $
              map (\cs -> (head cs, length cs)) $
              L.group $ L.sort $ nonAsciiChars
  mapM_ (\(c, count) -> U.putStrLn (c : ": " ++ show count)) table
