-- | Overloaded @null@ and @empty@ for collections and sequences.

module Agda.Utils.Null where

import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as ByteString
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set

class Null a where
  empty :: a
  null  :: a -> Bool
  -- ^ Satisfying @null empty == True@.

instance Null ByteString where
  empty = ByteString.empty
  null  = ByteString.null

instance Null [a] where
  empty = []
  null  = List.null

instance Null (Map k a) where
  empty = Map.empty
  null  = Map.null

instance Null (Seq a) where
  empty = Seq.empty
  null  = Seq.null

instance Null (Set a) where
  empty = Set.empty
  null  = Set.null

-- instance Null (Maybe a) where
--   empty = Nothing
--   null Nothing  = True
--   null (Just a) = False
