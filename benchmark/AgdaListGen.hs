{-# LANGUAGE CPP               #-}
module AgdaListGen where

import Data.List

theListLength :: Int
theListLength = len

#ifdef LSorted
#ifdef tail
theListDef = "theList = fromTo' " ++ show theListLength
#else
theListDef = "theList = fromTo " ++ show theListLength
#endif
#endif

#ifdef LRSorted
#ifdef tail
theListDef = "theList = downFrom' " ++ show theListLength
#else
theListDef = "theList = downFrom " ++ show theListLength
#endif
#endif
#ifdef LRandom
#ifdef tail
theListDef = "theList = downFromBbs' 43 " ++ show theListLength
#else
theListDef = "theList = fromToBbs 43 " ++ show theListLength
#endif
#endif

main = putStrLn $ unlines ["open import Prelude"
                          , "open import Extra"
                          , ""
                          , "theList : List Nat"
                          , theListDef]

