{-# LANGUAGE CPP               #-}
{-# LANGUAGE FlexibleInstances #-}

module RedBlack where

import System.Random

#ifdef RbUntyped
import           Untyped    (fromList)
#endif
#ifdef RbTyped
import           Typed      (fromList)
#endif
#ifdef RbTypedExist
import           TypedExist (fromList)
#endif

-- #ifdef LSorted
-- theList = [1..Len]
-- #endif
-- #ifdef LRSorted
-- theList = [Len, -1..1]
-- #endif

-- #ifdef LRandom
-- theList = take Len (randoms mkStdGen randSeed)
-- #endif
theList :: [Int]
theList = take len (randoms (mkStdGen randSeed))

randSeed = 0

-- We don't actually need to calculate the sum for the benchmark if we just
-- redirect the output to `/dev/null` the IO will not be an overhead. It might
-- actually be better *not* to calculate the sum because the `Foldable`
-- instances (that I defined) may be more or less efficient.
bench :: Int
bench = sum $ fromList theList

main :: IO ()
-- main = print . fromList $ longReversedList
main = print bench
