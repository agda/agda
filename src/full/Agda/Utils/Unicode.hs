
module Agda.Utils.Unicode
    ( isUnicodeId
    ) where

import Data.Char

-- Unicode ----------------------------------------------------------------

isUnicodeId :: Char -> Bool
isUnicodeId c = isPrint c && not (isAscii c)
