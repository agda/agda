
module Utils.Size ( Sized(..) ) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

class Sized a where
  size :: a -> Int

instance Sized [a] where
  size = length

instance Sized (Map k a) where
  size = Map.size

instance Sized (Set a) where
  size = Set.size

