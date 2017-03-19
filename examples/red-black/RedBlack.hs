{-# LANGUAGE FlexibleInstances #-}

module RedBlack where

#ifdef RbUntyped
import Untyped    (fromList)
#endif
#ifdef RbTyped
import Typed      (fromList)
#endif
#ifdef RbTypedExist
import TypedExist (fromList)
#endif

-- downFrom
longReversedList :: [Integer]
longReversedList = [h,h-1..0]
  where
    h = 1000000

-- We don't actually need to calculate the sum for the benchmark if we just
-- redirect the output to `/dev/null` the IO will not be an overhead. It might
-- actually be better *not* to calculate the sum because the `Foldable`
-- instances (that I defined) may be more or less efficient.
bench :: Integer
bench = sum $ fromList longReversedList

main :: IO ()
-- main = print . fromList $ longReversedList
main = print bench

instance Foldable Tree where
  foldr = undefined
