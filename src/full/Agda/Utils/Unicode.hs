
module Agda.Utils.Unicode
    ( UTF8
    , readFileUTF8
    , writeFileUTF8
    , toUTF8
    , fromUTF8
    , isUnicodeId
    ) where

import Data.Bits
import qualified Data.List as List
import Data.IntSet as Set
import Data.Char

import Agda.Utils.Monad ( (<$>) )

-- Unicode ----------------------------------------------------------------

isUnicodeId :: Char -> Bool
isUnicodeId c = isPrint c && not (isAscii c)

-- UTF-8 ------------------------------------------------------------------

type UTF8 = String

readFileUTF8 :: FilePath -> IO String
readFileUTF8 file = fromUTF8 . readAll <$> readFile file
  where readAll s = if s == s then s else s

writeFileUTF8 :: FilePath -> String -> IO ()
writeFileUTF8 file s = writeFile file $ toUTF8 s

toUTF8 :: String -> UTF8
toUTF8 = concatMap utf8
    where
	utf8 c
	    | n <= 0x7F	    = [c]
	    | n <= 0x7FF    = [ mk0 2 $ shiftR n 6
			      , mk1 n
			      ]
	    | n <= 0xFFFF   = [ mk0 3 $ shiftR n 12
			      , mk1 $ shiftR n 6
			      , mk1 n
			      ]
	    | n <= 0x1FFFFF = [ mk0 4 $ shiftR n 18
			      , mk1 $ shiftR n 12
			      , mk1 $ shiftR n 6
			      , mk1 n
			      ]
	    | n <= 0x3FFFFFF= [ mk0 3 $ shiftR n 24
			      , mk1 $ shiftR n 18
			      , mk1 $ shiftR n 12
			      , mk1 $ shiftR n 6
			      , mk1 n
			      ]
	    | n <= 0x7FFFFFF= [ mk0 2 $ shiftR n 30
			      , mk1 $ shiftR n 24
			      , mk1 $ shiftR n 18
			      , mk1 $ shiftR n 12
			      , mk1 $ shiftR n 6
			      , mk1 n
			      ]
	    | otherwise	    = error $ "toUTF8: invalid unicode character " ++ show c
	    where
		n	= fromEnum c
		--bits i    = reverse $ take i $ map (testBit n) [0..7]
		byte0 i	= foldl setBit 0 $ take i [7,6..0]
		byte1	= byte0 1
		mk0 i n	= toEnum $ byte0 i .|. n .&. mask (8 - i)
		mk1 n	= toEnum $ byte1 .|. n .&. mask 6

mask i	= foldl setBit 0 $ take i [0..]

fromUTF8 :: UTF8 -> String
fromUTF8 = List.map decode . chop
    where
	chop []	     = []
	chop s@(c:_) = w : chop s'
	    where
		(w,s') = splitAt len s
		n = fromEnum c
		len = case List.findIndex (not . testBit n) [7,6..0] of
			Just 0	-> 1
			Just 2	-> 2
			Just 3	-> 3
			Just 4	-> 4
-- 			Just 5	-> 5
-- 			Just 6	-> 6
			_	-> error $ "fromUTF8: Bad utf-8 character: " ++ show c
	decode [c]  = c
	decode cs   = toEnum buildAll
	    where
		build i k n = shiftL (mask i .&. n) k

		buildAll = foldr (.|.) (build i k n0) $
			   zipWith (build 6) [k-6,k-12..] ns
		    where
			i	= 7 - len
			len	= length cs
			k	= 6 * (len - 1)
			n0 : ns = List.map fromEnum cs


{-
showBits :: Char -> String
showBits c = unwords $ dropWhile (all (=='0')) $ chop 8 $ map f [31,30..0]
    where
	n = fromEnum c
	f i | testBit n i   = '1'
	    | otherwise	    = '0'
-}
