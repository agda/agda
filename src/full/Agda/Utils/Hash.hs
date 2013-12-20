{-| Instead of checking time-stamps we compute a hash of the module source and
    store it in the interface file. This module contains the functions to do
    that. -}
module Agda.Utils.Hash where

import Data.ByteString as B
import Data.Word
import qualified Data.Hash as H
import qualified Data.List as L

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
hashString :: String -> Integer
hashString = Prelude.foldr step 0
  where
    step c n = mod (fromIntegral (fromEnum c) * prime1 + n * prime2) prime3

    prime1 = 1230371
    prime2 = 446441
    prime3 = 275604541

