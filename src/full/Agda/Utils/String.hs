module Agda.Utils.String where

import Control.Monad.Reader
import Control.Monad.State


import Data.Char
import qualified Data.List as List
import Data.String



import Agda.Interaction.Options.IORefs ( UnicodeOrAscii(..) )
import Agda.Utils.List
import Agda.Utils.Suffix ( subscriptAllowed, toSubscriptDigit )

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

  escapeChars :: String
  escapeChars = "\"\\"

-- | Turns the string into a Haskell string literal, avoiding escape
-- codes.

haskellStringLiteral :: String -> String
haskellStringLiteral s = "\"" ++ concatMap escape s ++ "\""
  where
  escape c | c == '\n'         = "\\n"
           | c == '"'          = "\\\""
           | c == '\\'         = "\\\\"
           | ok c              = [c]
           | otherwise         = [c]

  ok c = case generalCategory c of
    UppercaseLetter -> True
    LowercaseLetter -> True
    TitlecaseLetter -> True
    _               -> isSymbol c || isPunctuation c

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
-- 0-9 unless the user explicitly asked us to not use any unicode characters.

showIndex :: (Show i, Integral i) => i -> String
showIndex = case subscriptAllowed of
  UnicodeOk -> map toSubscriptDigit . show
  AsciiOnly -> show

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
rtrim = List.dropWhileEnd isSpace

-- | Remove leading and trailing whitesapce.
trim :: String -> String
trim = rtrim . ltrim

instance (IsString (m a), Monad m) => IsString (ReaderT r m a) where
  fromString = lift . fromString

instance (IsString (m a), Monad m) => IsString (StateT s m a) where
  fromString = lift . fromString
