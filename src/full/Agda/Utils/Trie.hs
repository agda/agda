{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}

-- | Strict tries (based on "Data.Map.Strict" and "Agda.Utils.Maybe.Strict").

module Agda.Utils.Trie
  ( Trie
  , empty, singleton, insert, insertWith, union, unionWith, adjust, delete
  , toList, toAscList
  , lookupPath
  ) where

import Prelude hiding (Maybe(..), maybe, null)
import qualified Prelude as Lazy

import Data.Function
import Data.Functor
import Data.List (nubBy, sortBy, isPrefixOf)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Test.QuickCheck

import Agda.Utils.Maybe.Strict
import Agda.Utils.Null

-- | Finite map from @[k]@ to @v@.
--
--   With the strict 'Maybe' type, 'Trie' is also strict in 'v'.
data Trie k v = Trie !(Maybe v) !(Map k (Trie k v))
  deriving (Show, Eq)

-- | Empty trie.
instance Null (Trie k v) where
  empty = Trie Nothing Map.empty
  null (Trie v t) = null v && null t

-- | Singleton trie.
singleton :: [k] -> v -> Trie k v
singleton []     !v = Trie (Just v) Map.empty
singleton (x:xs) !v = Trie Nothing $ Map.singleton x (singleton xs v)

-- | Left biased union.
--
--   @union = unionWith (\ new old -> new)@.
union :: (Ord k) => Trie k v -> Trie k v -> Trie k v
union = unionWith const

-- | Pointwise union with merge function for values.
unionWith :: (Ord k) => (v -> v -> v) -> Trie k v -> Trie k v -> Trie k v
unionWith f (Trie v ss) (Trie w ts) =
  Trie (unionMaybeWith f v w) (Map.unionWith (unionWith f) ss ts)

-- | Insert.  Overwrites existing value if present.
--
--   @insert = insertWith (\ new old -> new)@
insert :: (Ord k) => [k] -> v -> Trie k v -> Trie k v
insert k v t = union (singleton k v) t

-- | Insert with function merging new value with old value.
insertWith :: (Ord k) => (v -> v -> v) -> [k] -> v -> Trie k v -> Trie k v
insertWith f k v t = unionWith f (singleton k v) t

-- | Delete value at key, but leave subtree intact.
delete :: Ord k => [k] -> Trie k v -> Trie k v
delete path = adjust path (const Nothing)

-- | Adjust value at key, leave subtree intact.
adjust :: Ord k => [k] -> (Maybe v -> Maybe v) -> Trie k v -> Trie k v
adjust path f t@(Trie v ts) =
  case path of
    -- case: found the value we want to adjust: adjust it!
    []                                 -> Trie (f v) ts
    -- case: found the subtrie matching the first key: adjust recursively
    k : ks | Lazy.Just s <- Map.lookup k ts -> Trie v $ Map.insert k (adjust ks f s) ts
    -- case: subtrie not found: leave trie untouched
    _ -> t

-- | Convert to ascending list.
toList :: Ord k => Trie k v -> [([k],v)]
toList = toAscList

-- | Convert to ascending list.
toAscList :: Ord k => Trie k v -> [([k],v)]
toAscList (Trie mv ts) = maybeToList (([],) <$> mv) ++
  [ (k:ks, v)
  | (k,  t) <- Map.toAscList ts
  , (ks, v) <- toAscList t
  ]

-- | Collect all values along a given path.
lookupPath :: Ord k => [k] -> Trie k v -> [v]
lookupPath xs (Trie v cs) = case xs of
    []     -> maybeToList v
    x : xs -> maybeToList v ++ Lazy.maybe [] (lookupPath xs) (Map.lookup x cs)

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

prop_path :: [Key] -> Model -> Property
prop_path ks m =
  collect (length $ modelPath ks m) $
  lookupPath ks (modelToTrie m) == modelPath ks m
