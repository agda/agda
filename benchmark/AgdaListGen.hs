{-# LANGUAGE CPP               #-}
module AgdaListGen where

import System.Random
import Data.List

theListLength :: Int
theListLength = len

theList :: [Int]
#ifdef LSorted
theList = [1..theListLength]
#endif
#ifdef LRSorted
theList = [theListLength, theListLength - 1..1]
#endif
#ifdef LRandom
theList = take theListLength (randomRs (0, 10^8) (mkStdGen randSeed))
#endif

main = putStrLn $ unlines ["open import Prelude", ""
                          , "theList : List Nat"
                          , "theList = " ++ showAgdaList theList]

showAgdaList :: Show a => [a] -> String
showAgdaList l = intercalate " ∷ " (map show l ++ ["[]"])

randSeed :: Int
randSeed = 0
