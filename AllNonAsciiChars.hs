-- | This module extracts all the non-ASCII characters used by the
-- library code.
--
-- The implementation relies on the utf8-string and FileManip
-- libraries which are available from Hackage.

module AllNonAsciiChars where

import qualified Data.List as L
import Data.Char
import Control.Applicative
import System.IO.UTF8 as U
import System.FilePath.Find

allNonAsciiChars :: IO String
allNonAsciiChars = do
  agdaFiles <- find (fileName /~? "_darcs")
                    (extension ~~? ".agda" ||? extension ~~? ".lagda")
                    "."
  L.sort . L.nub . filter (not . isAscii) . concat
    <$> mapM U.readFile agdaFiles

main = U.putStrLn =<< allNonAsciiChars
