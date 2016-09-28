
{-| Instead of checking time-stamps we compute a hash of the module source and
    store it in the interface file. This module contains the functions to do
    that. -}
module Agda.Utils.Hash where

import Data.ByteString as B
import Data.Word
import qualified Data.Hash as H
import qualified Data.List as L
import Data.Digest.Murmur64

import Agda.Utils.FileName

type Hash = Word64

hashByteString :: ByteString -> Hash
hashByteString = H.asWord64 . B.foldl' (\h b -> H.combine h (H.hashWord8 b)) (H.hashWord8 0)

hashFile :: AbsolutePath -> IO Hash
hashFile file = do
  s <- B.readFile (filePath file)
  return $ hashByteString s

combineHashes :: [Hash] -> Hash
combineHashes hs = H.asWord64 $ L.foldl' H.combine (H.hashWord8 0) $ L.map H.hash hs

-- | Hashing a module name for unique identifiers.
hashString :: String -> Word64
hashString = asWord64 . hash64

