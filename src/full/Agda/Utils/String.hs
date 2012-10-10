module Agda.Utils.String
  ( quote
  , showIndex
  , addFinalNewLine
  , indent
  ) where

import Data.List
import Numeric

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
indent i = unlines . map (genericReplicate i ' ' ++) . lines
