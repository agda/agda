-- | Tools for 3-way partitioning.

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

-- | Disjoint sum of three.
--
data Either3 a b c
  = In1 a
  | In2 b
  | In3 c
  deriving (Eq, Ord, Show)

-- | Partition a list into 3 groups.
--
--   Preserves the relative order or elements.
--
partitionEithers3 :: [Either3 a b c] -> ([a], [b], [c])
partitionEithers3 = \case
  []     -> ([], [], [])
  (x:xs) -> case x of
      In1 a -> (a:as, bs, cs)
      In2 b -> (as, b:bs, cs)
      In3 c -> (as, bs, c:cs)
    where (as, bs, cs) = partitionEithers3 xs

mapEither3M :: Applicative m => (a -> m (Either3 b c d)) -> [a] -> m ([b], [c], [d])
mapEither3M f xs = partitionEithers3 <$> traverse f xs

forEither3M :: Applicative m => [a] -> (a -> m (Either3 b c d)) -> m ([b], [c], [d])
forEither3M = flip mapEither3M
