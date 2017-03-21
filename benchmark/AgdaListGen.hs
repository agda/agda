{-# LANGUAGE CPP               #-}
module AgdaListGen where

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
theListDef = "theList = downFromBbs 43 " ++ show theListLength
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
