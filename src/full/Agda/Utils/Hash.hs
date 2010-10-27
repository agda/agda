
module Agda.Utils.Hash where

hash :: String -> Integer
hash = foldr step 0
  where
    step c n = mod (fromIntegral (fromEnum c) * prime1 + n * prime2) prime3

    prime1 = 1230371
    prime2 = 446441
    prime3 = 275604541
