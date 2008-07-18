module Agda.Utils.String
  ( quote
  , addFinalNewLine
  ) where

-- | 'quote' adds double quotes around the string, and escapes double
-- quotes and backslashes within the string. This is different from
-- the behaviour of 'show':
--
-- @
-- \> 'putStrLn' $ 'Agda.Utils.Unicode.toUTF8' $ 'show' \"\\x2200\"
-- \"\\8704\"
-- \> 'putStrLn' $ 'Agda.Utils.Unicode.toUTF8' $ 'quote' \"\\x2200\"
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
