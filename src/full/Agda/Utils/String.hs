module Agda.Utils.String
  ( quote
  , addFinalNewLine
  , indent
  ) where

import Data.List

-- | 'quote' adds double quotes around the string, and escapes double
-- quotes and backslashes within the string. This is different from
-- the behaviour of 'show':
--
-- @
-- \> 'System.IO.UTF8.putStrLn' $ 'show' \"\\x2200\"
-- \"\\8704\"
-- \> 'System.IO.UTF8.putStrLn' $ 'quote' \"\\x2200\"
-- \"&#x2200;\"
-- @

quote :: String -> String
quote s = "\"" ++ concatMap escape s ++ "\""
  where
  escape c | c `elem` escapeChars = ['\\', c]
           | otherwise            = [c]

  escapeChars = "\"\\"

-- | Adds a final newline if there is not already one.

addFinalNewLine :: String -> String
addFinalNewLine "" = "\n"
addFinalNewLine s | last s == '\n' = s
                  | otherwise      = s ++ "\n"

-- | Indents every line the given number of steps.

indent :: Integral i => i -> String -> String
indent i = unlines . map (genericReplicate i ' ' ++) . lines
