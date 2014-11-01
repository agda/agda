{-# OPTIONS_GHC -fwarn-missing-signatures #-}

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
