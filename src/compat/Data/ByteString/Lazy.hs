
module Data.ByteString.Lazy
    ( ByteString
    , null, tail, head, splitAt
    , hGetContents
    , unpack
    ) where

import Prelude hiding (head)
import qualified Prelude
import System.IO

type ByteString = String

unpack :: ByteString -> [Int]
unpack = map fromEnum

head :: ByteString -> Int
head = fromEnum . Prelude.head
