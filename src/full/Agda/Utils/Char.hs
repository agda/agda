{-# OPTIONS_GHC -Wunused-imports #-}

-- |
-- Agda strings uses Data.Text [1], which can only represent unicode scalar values [2], excluding
-- the surrogate code points [3] (@U+D800..U+DFFF@). To allow @primStringFromList@ to be injective
-- we make sure character values also exclude surrogate code points, mapping them to the replacement
-- character @U+FFFD@.
--
-- See #4999 for more information.
--
-- [1] https://hackage.haskell.org/package/text-1.2.4.0/docs/Data-Text.html#g:2
-- [2] https://www.unicode.org/glossary/#unicode_scalar_value
-- [3] https://www.unicode.org/glossary/#surrogate_code_point

module Agda.Utils.Char where

import Data.Char

-- | The unicode replacement character � .
replacementChar :: Char
replacementChar = '\xFFFD'

-- | Is a character a surrogate code point.
isSurrogateCodePoint :: Char -> Bool
isSurrogateCodePoint c = generalCategory c == Surrogate

-- | Map surrogate code points to the unicode replacement character.
replaceSurrogateCodePoint :: Char -> Char
replaceSurrogateCodePoint c
  | isSurrogateCodePoint c = replacementChar
  | otherwise              = c

-- | Total function to convert an integer to a character. Maps surrogate code points
--   to the replacement character @U+FFFD@.
integerToChar :: Integer -> Char
integerToChar = replaceSurrogateCodePoint . toEnum . fromIntegral . (`mod` 0x110000)

