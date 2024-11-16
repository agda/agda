{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.Trie ( tests ) where

import Agda.Utils.Trie

import Data.Function ( on )
import Data.List ( nubBy, sortBy, isPrefixOf, inits )

import Prelude hiding ( lookup, filter )
import qualified Prelude

import Internal.Helpers

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

prop_lookup :: [Key] -> Model -> Bool
prop_lookup ks m@(Model ksvs) =
  lookup ks (modelToTrie m) == Prelude.lookup ks ksvs

modelPath :: [Key] -> Model -> [Val]
modelPath ks (Model xs) =
  map snd
  $ sortBy (compare `on` length . fst)
  $ nubBy ((==) `on` fst)
  $ Prelude.filter (flip isPrefixOf ks . fst) xs

prop_path :: [Key] -> Model -> Property
prop_path ks m =
  collect (length $ modelPath ks m) $
  lookupPath ks (modelToTrie m) == modelPath ks m

prop_everyPrefix :: [Integer] -> Integer -> Bool
prop_everyPrefix ks v =
  everyPrefix ks v ==
  foldr union empty [ singleton ks' v | ks' <- inits ks ]

-- Andreas 2024-11-16: delete is as of now not the inverse of insert
-- because it does not clean up the Trie.
-- It should remove the subtrees that do not contain a single value,
-- but does not.
-- E.g.
-- @
--    t  := insert [a,b] v empty = Nothing --a--> Nothing --b--> Just v
--    t' := delete [a,b] t       = Nothing --a--> Nothing --b--> Nothing
--    t == t' = False
-- @
-- Fixing the representation of tries would fix this test:
--
-- prop_insert_delete :: Model -> [Key] -> Val -> Property
-- prop_insert_delete m k v = not (member k t) ==> delete k (insert k v t) == t
--   where
--     t = modelToTrie m

-- Test whether @null@ is robust wrt. non-canonical tries.
prop_empty_insert_delete :: [Key] -> Val -> Bool
prop_empty_insert_delete k v = null $ delete k $ insert k v empty

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'allProperties'.
--
-- Using 'allProperties' is convenient and superior to the manual
-- enumeration of tests, since the name of the property is added
-- automatically.

tests :: TestTree
tests = testProperties "Internal.Utils.Trie" $allProperties
