{-| Instead of checking time-stamps we compute a hash of the module source and
    store it in the interface file. This module contains the functions to do
    that. -}
module Agda.Utils.Hash where

import Data.Hashable
import Data.ByteString as B
import Data.Word

import Agda.Utils.FileName

type Hash = Word64

hash64 :: ByteString -> Hash
hash64 = fromIntegral . hash

hashFile :: AbsolutePath -> IO Hash
hashFile file = do
  s <- B.readFile (filePath file)
  return $ hash64 s

combineHashes :: [Hash] -> Hash
combineHashes = fromIntegral . hash

-- | Hashing a module name for unique identifiers.
hashString :: String -> Integer
hashString = Prelude.foldr step 0
  where
    step c n = mod (fromIntegral (fromEnum c) * prime1 + n * prime2) prime3

    prime1 = 1230371
    prime2 = 446441
    prime3 = 275604541

