
module Agda.Utils.Unicode
    ( isUnicodeId
    , convertLineEndings
    ) where

import Data.Char

-- Unicode ----------------------------------------------------------------

isUnicodeId :: Char -> Bool
isUnicodeId c = isPrint c && not (isAscii c)

-- | Converts many character sequences which may be interpreted as
-- line or paragraph separators into '\n'.

convertLineEndings :: String -> String
convertLineEndings ('\x000D' : '\x000A' : s) = '\n' : convertLineEndings s
convertLineEndings ('\x000A'            : s) = '\n' : convertLineEndings s
convertLineEndings ('\x000D'            : s) = '\n' : convertLineEndings s
convertLineEndings ('\x0085'            : s) = '\n' : convertLineEndings s
convertLineEndings ('\x000C'            : s) = '\n' : convertLineEndings s
convertLineEndings ('\x2028'            : s) = '\n' : convertLineEndings s
convertLineEndings ('\x2029'            : s) = '\n' : convertLineEndings s
convertLineEndings (c                   : s) = c    : convertLineEndings s
convertLineEndings ""                        = ""
