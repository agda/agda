
module Agda.Utils.Size ( Sized(..) ) where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List

class Sized a where
  size :: Integral n => a -> n

instance Sized [a] where
  size = genericLength

instance Sized (Map k a) where
  size = fromIntegral . Map.size

instance Sized (Set a) where
  size = fromIntegral . Set.size

instance Sized a => Sized (Maybe a) where
  size Nothing  = 1
  size (Just a) = size a
