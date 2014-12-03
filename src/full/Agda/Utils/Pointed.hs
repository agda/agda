-- RETIRED in favor of Agda.Utils.Singleton

module Agda.Utils.Pointed where

import Data.Set

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

instance Pointed Set where
  point = singleton
