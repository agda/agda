
module Stack where

import Data.Monoid

infixl 5 :<, +<

data Stack a = Empty | Stack a :< a
  deriving (Eq, Ord)

instance Monoid (Stack a) where
  mempty = Empty
  mappend xs Empty     = xs
  mappend xs (ys :< y) = mappend xs ys :< y

(+<) :: Stack a -> Stack a -> Stack a
(+<) = mappend

toList :: Stack a -> [a]
toList = reverse . list where
  list (xs :< x) = x : list xs
  list Empty     = []

fromList :: [a] -> Stack a
fromList = foldl (:<) Empty

instance Show a => Show (Stack a) where
  show = show . toList
