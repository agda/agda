{-# LANGUAGE CPP               #-}
module AgdaListGen where

import System.Random
import Data.List

theListLength :: Int
theListLength = len

#ifdef LSorted
theListDef = "theList = fromTo " ++ show theListLength
#endif
#ifdef LRSorted
theListDef = "theList = downFrom " ++ show theListLength
#endif
#ifdef LRandom
theList :: [Int]
theList = take theListLength (randomRs (0, 10^8) (mkStdGen randSeed))
theListDef = "theList = " ++ showAgdaList theList
#endif

main = putStrLn $ unlines ["open import Prelude"
                          , "open import Extra"
                          , ""
                          , "theList : List Nat"
                          , theListDef]

showAgdaList :: Show a => [a] -> String
showAgdaList l = intercalate " ∷ " (map show l ++ ["[]"])

randSeed :: Int
randSeed = 0
