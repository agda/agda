module Agda.Utils.Pointed where

-- | Pointed class.
--
--   We could have used Data.Pointed by Edward Kmett, but it has a
--   lot of package dependencies.
class Pointed f where
  point :: a -> f a

instance Pointed [] where
  point a = [a]

instance Pointed Maybe where
  point = Just
