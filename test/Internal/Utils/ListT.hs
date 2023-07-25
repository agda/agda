{-# LANGUAGE TemplateHaskell #-}

-- | Quickcheck properties for 'Agda.Utils.ListT'.

module Internal.Utils.ListT ( tests ) where

import Control.Applicative

import Data.Functor.Identity
import Data.Word (Word8)

import Text.Show.Functions

import Agda.Utils.ListT

import Internal.Helpers

------------------------------------------------------------------------------
-- * Identity monad instance of ListT (simply lists)

type List = ListT Identity

foldList :: (a -> b -> b) -> b -> List a -> b
foldList cons nil l = runIdentity $ foldListT c (Identity nil) l
  where c a = Identity . cons a . runIdentity

fromList :: [a] -> List a
fromList = foldr consListT nilListT

toList :: List a -> [a]
toList = foldList (:) []

-- Pick a medium-sized type where collisions are not very unlikely.
type A = Word8
type B = Word8

prop_concat :: [[A]] -> Bool
prop_concat xxs = toList (concatListT (fromList (map fromList xxs))) == concat xxs

prop_idiom :: [A -> B] -> [A] -> Bool
prop_idiom fs xs = toList (fromList fs <*> fromList xs) == (fs <*> xs)

prop_concatMap :: (A -> [B]) -> [A] -> Bool
prop_concatMap f xs = toList (fromList . f =<< fromList xs) == (f =<< xs)

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
tests = testProperties "Internal.Utils.ListT" $allProperties
