module Hello.World where

import Prelude hiding (last, replicate)

last :: [a] -> a
last [a]    = a
last (a:as) = last as

replicate :: Integer -> a -> [a]
replicate n a
  | n > 0     = a : replicate (n-1) a
  | otherwise = []

-- Involving recursive functions to prevent GHC from inlining this into the executable.
helloWorld :: Integer -> IO ()
helloWorld n = putStrLn $ last $ replicate n "Hello, world!"
