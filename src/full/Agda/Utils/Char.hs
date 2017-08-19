module Agda.Utils.Char where

import Data.Char

-- | Convert a character in @'0'..'9'@ into the corresponding digit @0..9@.

decDigit :: Char -> Int
decDigit c = ord c - ord '0'

-- | Convert a character in @'0'..'9','A'..'F','a'..'f'@
--   into the corresponding digit @0..15@.

hexDigit :: Char -> Int
hexDigit c | isDigit c  = decDigit c
           | otherwise  = ord (toLower c) - ord 'a' + 10

-- | Convert a character in @'0'..'7'@ into the corresponding digit @0..7@.

octDigit :: Char -> Int
octDigit = decDigit

------------------------------------------------------------------------
-- * Unicode exploration
------------------------------------------------------------------------

-- | Unicode characters are divided into letters, numbers, marks,
-- punctuation, symbols, separators (including spaces) and others
-- (including control characters).
--
-- These are the tests that 'Data.Char' offers:
data UnicodeTest
  = IsControl | IsSpace
  | IsLower | IsUpper | IsAlpha | IsAlphaNum | IsPrint
  | IsDigit | IsOctDigit | IsHexDigit
  | IsLetter | IsMark | IsNumber | IsPunctuation | IsSymbol | IsSeparator
  deriving (Eq, Ord, Show)

-- | Test names paired with their implementation.
unicodeTests :: [(UnicodeTest, Char -> Bool)]
unicodeTests =
  [ (IsControl, isControl), (IsSpace, isSpace)
  , (IsLower, isLower), (IsUpper, isUpper), (IsAlpha, isAlpha)
  , (IsAlphaNum, isAlphaNum)
  , (IsPrint, isPrint)
  , (IsDigit, isDigit), (IsOctDigit, isOctDigit), (IsHexDigit, isHexDigit)
  , (IsLetter, isLetter), (IsMark, isMark)
  , (IsNumber, isNumber), (IsPunctuation, isPunctuation), (IsSymbol, isSymbol)
  , (IsSeparator, isSeparator)
  ]

-- | Find out which tests a character satisfies.
testChar :: Char -> [UnicodeTest]
testChar c = map fst $ filter (($ c) . snd) unicodeTests
