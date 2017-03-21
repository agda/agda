{-# LANGUAGE CPP               #-}
{-# LANGUAGE FlexibleInstances #-}

module RedBlack where

import System.Random

#ifdef RbUntyped
import           Untyped    (fromList, toList)
#endif
#ifdef RbTyped
import           Typed      (fromList, toList)
#endif
#ifdef RbTypedExist
import           TypedExist (fromList, toList)
#endif

theList :: [Int]
#ifdef LSorted
theList = [1..Len]
#endif
#ifdef LRSorted
theList = [Len, Len-1..1]
#endif
#ifdef LRandom
theList = take Len (randoms mkStdGen randSeed)
#endif

randSeed = 0

-- We don't actually need to calculate the sum for the benchmark if we just
-- redirect the output to `/dev/null` the IO will not be an overhead. It might
-- actually be better *not* to calculate the sum because the `Foldable`
-- instances (that I defined) may be more or less efficient.
bench :: Int
bench = sum $ toList $ fromList theList

main :: IO ()
main = print bench
