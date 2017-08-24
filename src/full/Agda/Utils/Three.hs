-- | Tools for a 3-element type.

module Agda.Utils.Three where

-- | Enum type with 3 elements.
--
data Three
  = One
  | Two
  | Three
  deriving (Eq, Ord, Show, Bounded, Enum)

-- | Partition a list into 3 groups.
--
--   Preserves the relative order or elements.
--
partition3 :: (a -> Three) -> [a] -> ([a], [a], [a])
partition3  f = loop where
  loop []     = ([], [], [])
  loop (x:xs) = case f x of
      One   -> (x:as, bs, cs)
      Two   -> (as, x:bs, cs)
      Three -> (as, bs, x:cs)
    where (as, bs, cs) = loop xs
