-- | Invertible maps from lists to enums.

module Agda.Utils.BiMapTrieEnum where

import           Prelude                hiding (null)

import           GHC.Generics           ( Generic )
import           Control.DeepSeq        ( NFData )

import           Data.EnumMap.Strict    ( EnumMap )
import qualified Data.EnumMap.Strict    as EnumMap
import           Data.These             ( These(This, That, These) )

import           Agda.Utils.Null
import           Agda.Utils.Trie        ( Trie )
import qualified Agda.Utils.Trie        as Trie

-- | Bimaps from lists to enums.
--
data BiMapTrieEnum k v = BiMapTrieEnum
  { bmTrie    :: Trie k v
      -- ^ Map from lists of @k@ to enums @v@.
  , bmEnumMap :: EnumMap v [k]
      -- ^ Map from enums @v@ to lists of @k@.
  } deriving (Show, Generic)

-- * Empty

instance Null (BiMapTrieEnum k v) where
  empty = BiMapTrieEnum empty empty
  null (BiMapTrieEnum t m) = null t && null m

-- * Lookup

lookup :: Ord k => [k] -> BiMapTrieEnum k v -> Maybe v
lookup k = Trie.lookup k . bmTrie

lookupInv :: Enum v => v -> BiMapTrieEnum k v -> Maybe [k]
lookupInv v = EnumMap.lookup v . bmEnumMap

-- * Insert

data KeyAlreadyPresent v = KeyAlreadyPresent v
data ValueAlreadyPresent k = ValueAlreadyPresent [k]

type InsertError k v = These (KeyAlreadyPresent v) (ValueAlreadyPresent k)

-- | Insert key-value pair.
--
--   If any of these is present already, return an error.
--
insert' :: (Ord k, Enum v)
  => [k] -> v -> BiMapTrieEnum k v -> Either (InsertError k v) (BiMapTrieEnum k v)
insert' k v b@(BiMapTrieEnum t m) =
  case (Trie.lookup k t, EnumMap.lookup v m) of
    (Nothing, Nothing) -> Right $ insert k v b
    (Just v', Nothing) -> Left $ This  (KeyAlreadyPresent v')
    (Nothing, Just k') -> Left $ That                         (ValueAlreadyPresent k')
    (Just v', Just k') -> Left $ These (KeyAlreadyPresent v') (ValueAlreadyPresent k')

-- | Insert key-value pair, both must be absent.
--   If any of these is present, the integrity of the bimap might be destroyed.
--
insert :: (Ord k, Enum v) => [k] -> v -> BiMapTrieEnum k v -> BiMapTrieEnum k v
insert k v (BiMapTrieEnum t m) = BiMapTrieEnum (Trie.insert k v t) (EnumMap.insert v k m)

-- Boring instances

instance (NFData k, NFData v) => NFData (BiMapTrieEnum k v)
