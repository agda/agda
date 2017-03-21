{-# LANGUAGE CPP               #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}

module RedBlack where

import Data.List (foldl')

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
-- theList = take Len (randoms (mkStdGen randSeed))
theList = downFromBbs 43 Len
#endif

blumblumshub :: Int -> Int -> Int
blumblumshub xn m = mod (xn ^ 2) m

downFromBbs :: Int -> Int -> [Int]
downFromBbs seed = f seed []
  where
  f _ acc 0       = acc
  f !x !acc l = f (blumblumshub x m) (x : acc) (l - 1)
    where
      m           = m17 * m31
      m17         = 2971
      m31         = 4111

randSeed = 0

-- We don't actually need to calculate the sum for the benchmark if we just
-- redirect the output to `/dev/null` the IO will not be an overhead. It might
-- actually be better *not* to calculate the sum because the `Foldable`
-- instances (that I defined) may be more or less efficient.
treeSort :: Ord a => [a] -> [a]
treeSort = toList . fromList

bench :: Int
bench = sum' $ treeSort theList
-- bench = sum' $ theList

sum' :: [Int] -> Int
sum' = foldl' (+) 0

main :: IO ()
main = print bench
