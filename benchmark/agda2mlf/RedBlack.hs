{-# LANGUAGE CPP               #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}

module RedBlack where

import Data.List (foldl')
import Extra

#ifdef RbUntyped
import           Untyped
#endif
#ifdef RbTyped
import           Typed
#endif
#ifdef RbTypedExist
import           TypedExist
#endif

len :: Int
len = Len

theList :: [Int]
#ifdef LSorted
#ifdef tail
theList = fromTo' len
#else
theList = fromTo len
#endif
#endif
#ifdef LRSorted
#ifdef tail
theList = downFrom' len
#else
theList = downFrom len
#endif
#endif
#ifdef LRandom
#ifdef tail
theList = downFromBbs' 43 len
#else
theList = fromToBbs 43 len
#endif
#endif

myFromList :: Ord a => [a] -> Tree a
#ifdef strict
myFromList = fromList'
#else
myFromList = fromList
#endif


-- We don't actually need to calculate the sum for the benchmark if we just
-- redirect the output to `/dev/null` the IO will not be an overhead. It might
-- actually be better *not* to calculate the sum because the `Foldable`
-- instances (that I defined) may be more or less efficient.
treeSort :: Ord a => [a] -> [a]
treeSort = toList . myFromList

bench :: Int
bench = sum' $ treeSort theList
-- bench = sum' $ theList

sum' :: [Int] -> Int
sum' = foldl' (+) 0

main :: IO ()
main = print bench
