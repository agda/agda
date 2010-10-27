
module Agda.Utils.Char where

import Data.Char

decDigit :: Char -> Int
decDigit c = ord c - ord '0'

hexDigit :: Char -> Int
hexDigit c | isDigit c	= decDigit c
           | otherwise	= ord (toLower c) - ord 'a' + 10

octDigit :: Char -> Int
octDigit = decDigit
