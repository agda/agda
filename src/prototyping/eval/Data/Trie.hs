{-# OPTIONS_GHC -fglasgow-exts #-}
module Data.Trie where

import Prelude hiding (lookup)
import qualified Data.Map as Map
import qualified Data.List as List
import Data.Map (Map)
import Data.Maybe
import Data.Typeable
import Data.Generics
import Test.QuickCheck

(f -*- g) (x, y) = (f x, g y)
(f `on` g) x y	 = f (g x) (g y)

data Trie k a = Node (Maybe a) !(Map k (Trie k a))
    deriving (Eq, Ord, Show, Typeable, Data)

empty :: Trie k a
empty = Node Nothing Map.empty

singleton :: Ord k => [k] -> a -> Trie k a
singleton k v = insert k v empty

size :: Ord k => Trie k a -> Int
size (Node v m) = maybe 0 (const 1) v + sum (List.map size $ Map.elems m)

insert :: Ord k => [k] -> a -> Trie k a -> Trie k a
insert []     v (Node _ m) = Node (Just v) m
insert (x:xs) v (Node w m) = Node w $ Map.insertWith (\_ -> insert xs v) x (singleton xs v) m

delete :: Ord k => [k] -> Trie k a -> Trie k a
delete []     (Node _ m) = Node Nothing m
delete (x:xs) (Node w m) = Node w $ Map.adjust (delete xs) x m

lookup :: Ord k => [k] -> Trie k a -> Maybe a
lookup []     (Node r _) = r
lookup (x:xs) (Node _ m) = lookup xs =<< Map.lookup x m

member :: Ord k => [k] -> Trie k a -> Bool
member k t = isJust $ lookup k t

fromList :: Ord k => [([k], a)] -> Trie k a
fromList = foldr (uncurry insert) empty

toList :: Ord k => Trie k a -> [([k], a)]
toList (Node v m) = el v ++ concat (map rest $ Map.toList m)
    where
	el Nothing  = []
	el (Just v) = [([], v)]
	rest (k, t) = map ((k:) -*- id) $ toList t

instance (Ord k, Arbitrary k, Arbitrary a) => Arbitrary (Trie k a) where
    arbitrary = fmap fromList arbitrary
    coarbitrary = coarbitrary . toList

newtype Lower = Lower { unLower :: Char }
    deriving (Eq, Ord)

instance Show Lower where
    show     = show . unLower
    showList = shows . map unLower

instance Arbitrary Lower where
    arbitrary	= elements $ map Lower $ ['a'..'f']
    coarbitrary = coarbitrary . fromEnum . unLower

prop_fromToList :: [([Lower], Int)] -> Bool
prop_fromToList xs = xs' == List.sort (toList $ fromList xs)
    where
	xs' = List.sort $ List.nubBy ((==) `on` fst) xs

prop_toFromList :: Trie Lower Int -> Bool
prop_toFromList t = t == fromList (toList t)

prop_size :: Trie Lower Int -> Bool
prop_size t = size t == length (toList t)

prop_insertLookup :: [Lower] -> Int -> Trie Lower Int -> Bool
prop_insertLookup x n t = lookup x (insert x n t) == Just n

prop_deleteLookup :: [Lower] -> Trie Lower Int -> Property
prop_deleteLookup x t = member x t ==> lookup x (delete x t) == Nothing

-- more tests should follow
