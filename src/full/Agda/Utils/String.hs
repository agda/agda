module Agda.Utils.String where

import Data.Char
import qualified Data.List as List

import Numeric

import Agda.Utils.List

-- | 'quote' adds double quotes around the string, replaces newline
-- characters with @\n@, and escapes double quotes and backslashes
-- within the string. This is different from the behaviour of 'show':
--
-- @
-- \> 'putStrLn' $ 'show' \"\\x2200\"
-- \"\\8704\"
-- \> 'putStrLn' $ 'quote' \"\\x2200\"
-- \"∀\"
-- @
--
-- (The code examples above have been tested using version 4.2.0.0 of
-- the base library.)

quote :: String -> String
quote s = "\"" ++ concatMap escape s ++ "\""
  where
  escape c | c == '\n'            = "\\n"
           | c `elem` escapeChars = ['\\', c]
           | otherwise            = [c]

  escapeChars = "\"\\"

-- | Adds hyphens around the given string
--
-- >>> putStrLn $ delimiter "Title"
-- ———— Title —————————————————————————————————————————————————

delimiter :: String -> String
delimiter s = concat [ replicate 4 '\x2014'
                     , " ", s, " "
                     , replicate (54 - length s) '\x2014'
                     ]


-- | Shows a non-negative integer using the characters ₀-₉ instead of
-- 0-9.

showIndex :: (Show i, Integral i) => i -> String
showIndex n =
  showIntAtBase 10 (\i -> toEnum (i + fromEnum '\x2080')) n ""

-- | Adds a final newline if there is not already one.

addFinalNewLine :: String -> String
addFinalNewLine "" = "\n"
addFinalNewLine s | last s == '\n' = s
                  | otherwise      = s ++ "\n"

-- | Indents every line the given number of steps.

indent :: Integral i => i -> String -> String
indent i = unlines . map (List.genericReplicate i ' ' ++) . lines

newtype Str = Str { unStr :: String }
  deriving Eq

instance Show Str where
  show = unStr

-- | Show a number using comma to separate powers of 1,000.

showThousandSep :: Show a => a -> String
showThousandSep = reverse . List.intercalate "," . chop 3 . reverse . show

-- | Remove leading whitespace.
ltrim :: String -> String
ltrim = dropWhile isSpace

-- | Remove trailing whitespace.
rtrim :: String -> String
rtrim = reverse . ltrim . reverse

-- | Remove leading and trailing whitesapce.
trim :: String -> String
trim = rtrim . ltrim
