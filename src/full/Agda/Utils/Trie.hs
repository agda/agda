-----------------------------------------------------------------------------
-- |
-- Module      :  Unstable.Org.Lochan.Trie
-- Copyright   :  (c) Keith Wansbrough 2005
-- License     :  BSD-style
-- 
-- Maintainer  :  keith.hlib at lochan.org
--             :  modified and extended by Ulf Norell
-- Stability   :  experimental
-- Portability :  portable
--
--  This module provides a very basic implementation of the Trie data type,
--  with no great concern for efficiency, or for completeness of API.
--
-----------------------------------------------------------------------------

module Agda.Utils.Trie
    (
    -- * Data type
    Trie,
    -- * Constructors
    empty, singleton, union, unionWith,
    insert, insertWith,
    -- * Primitive accessors and mutators
    value, children, value_u, children_u,
    lookup, lookupPath,
    -- * Basic operations
    preOrder, upwards, downwards,
    -- * Derived operations
    takeWhile, takeWhile_V, fringe,
    ) where
                

import Prelude hiding (takeWhile, lookup)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Control.Monad

-- |A Trie with key elements of type @k@ (keys of type @[k]@) and values of type @v@.
data Trie k v = Trie { value    :: Maybe v
                     , children :: Map k (Trie k v)
                     }
  deriving Show

-- |Modify the 'children' field of a trie.
value_u :: (Maybe v -> Maybe v) -> Trie k v -> Trie k v
value_u f p = p { value = f (value p) }

-- |Modify the 'children' field of a trie.
children_u :: (Map k (Trie k v) -> Map k (Trie k v)) -> Trie k v -> Trie k v
children_u f p = p { children = f (children p) }

-- |The empty trie.
empty :: Trie k v
empty = Trie { value = Nothing, children = Map.empty }

-- |The singleton trie.
singleton :: Ord k => [k] -> v -> Trie k v
singleton [] x     = Trie { value = Just x, children = Map.empty }
singleton (k:ks) x = Trie { value = Nothing, children = Map.singleton k (singleton ks x) }

-- |Combining two tries.  The first shadows the second.
union :: Ord k => Trie k v -> Trie k v -> Trie k v
union p1 p2 =
    Trie {
          value    = mplus (value p1) (value p2),
          children = Map.unionWith union (children p1) (children p2)
         }

-- |Combining two tries.  If the two define the same key, the
-- specified combining function is used.
unionWith :: Ord k => (v -> v -> v) -> Trie k v -> Trie k v -> Trie k v
unionWith f p1 p2 =
    Trie { value    = lift f (value p1) (value p2)
         , children = Map.unionWith (unionWith f) (children p1) (children p2)
         }
    where lift _ Nothing y = y
          lift _ x Nothing = x
          lift _ (Just x) (Just y) = Just (f x y)
    

-- |Insertion.
insert :: Ord k => [k] -> v -> Trie k v -> Trie k v
insert k v t = union (singleton k v) t

insertWith :: Ord k => (v -> v -> v) -> [k] -> v -> Trie k v -> Trie k v
insertWith f k v t = unionWith f (singleton k v) t

-- |Lookup an element.
lookup :: Ord k => [k] -> Trie k v -> Maybe v
lookup []       t = value t
lookup (k : ks) t = lookup ks =<< Map.lookup k (children t)

-- |Lookup and return all values on the path.
lookupPath :: Ord k => [k] -> Trie k v -> [v]
lookupPath ks t = case ks of
  []     -> list $ value t
  k : ks -> concat $ list (value t) : list (fmap (lookupPath ks) (Map.lookup k $ children t))
  where
    list = maybe [] (:[])

-- |Enumerate all (key,value) pairs, in preorder.
preOrder :: Ord k => [k] -> Trie k v -> [([k],v)]
preOrder ks p = getNode p
                ++ concatMap (\(k,p') -> preOrder (ks++[k]) p')
                             (Map.toList (children p))
    where getNode p = maybe [] (\ v -> [(ks,v)]) (value p)

-- |An upwards accumulation on the trie.
upwards :: Ord k => (Trie k v -> Trie k v) -> Trie k v -> Trie k v
upwards f = f . children_u (Map.map (upwards f))

-- |A downwards accumulation on the trie.
downwards :: Ord k => (Trie k v -> Trie k v) -> Trie k v -> Trie k v
downwards f = children_u (Map.map (downwards f)) . f

-- |Return the prefix of the trie satisfying @f@.
takeWhile :: Ord k => (Trie k v -> Bool) -> Trie k v -> Trie k v
takeWhile f = downwards (children_u (Map.filter f))

-- |Return the prefix of the trie satisfying @f@ on all values present.
takeWhile_V :: Ord k => (v -> Bool) -> Trie k v -> Trie k v
takeWhile_V f = takeWhile (maybe True f . value)

-- |Return the fringe of the trie (the trie composed of only the leaf nodes).
fringe :: Ord k => Trie k v -> Trie k v
fringe = upwards (\ p -> if Map.null (children p) then p else value_u (const Nothing) p)


