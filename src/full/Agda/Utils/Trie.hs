
module Agda.Utils.Trie
  ( Trie
  , empty, singleton, insert, lookupPath, union
  ) where

import Control.Applicative hiding (empty)
import Control.Monad (mplus)
import Data.Function
import Data.List (nubBy, sortBy, isPrefixOf)
import Data.Map (Map)
import qualified Data.Map as Map
import Test.QuickCheck

data Trie k v = Trie (Maybe v) (Map k (Trie k v))
  deriving Show

empty :: Trie k v
empty = Trie Nothing Map.empty

singleton :: [k] -> v -> Trie k v
singleton []     v = Trie (Just v) Map.empty
singleton (x:xs) v = Trie Nothing $ Map.singleton x (singleton xs v)

-- | Left biased union.
union :: Ord k => Trie k v -> Trie k v -> Trie k v
union (Trie v ss) (Trie w ts) =
  Trie (v `mplus` w) (Map.unionWith union ss ts)

insert :: Ord k => [k] -> v -> Trie k v -> Trie k v
insert k v t = union (singleton k v) t

lookupPath :: Ord k => [k] -> Trie k v -> [v]
lookupPath xs (Trie v cs) = case xs of
    []     -> val v
    x : xs -> val v ++ maybe [] (lookupPath xs) (Map.lookup x cs)
  where
    val = maybe [] (:[])

-- Tests ------------------------------------------------------------------

newtype Key = Key Int
  deriving (Eq, Ord)

newtype Val = Val Int
  deriving (Eq)

newtype Model = Model [([Key], Val)]
  deriving (Eq, Show)

instance Show Key where
  show (Key x) = show x

instance Show Val where
  show (Val x) = show x

instance Arbitrary Key where
  arbitrary = elements $ map Key [1..2]
  shrink (Key x) = Key <$> shrink x

instance Arbitrary Val where
  arbitrary = elements $ map Val [1..3]
  shrink (Val x) = Val <$> shrink x

instance Arbitrary Model where
  arbitrary = Model <$> arbitrary
  shrink (Model xs) = Model <$> shrink xs

modelToTrie :: Model -> Trie Key Val
modelToTrie (Model xs) = foldr (uncurry insert) empty xs

modelPath :: [Key] -> Model -> [Val]
modelPath ks (Model xs) =
  map snd
  $ sortBy (compare `on` length . fst)
  $ nubBy ((==) `on` fst)
  $ filter (flip isPrefixOf ks . fst) xs

prop_path ks m =
  collect (length $ modelPath ks m) $
  lookupPath ks (modelToTrie m) == modelPath ks m
