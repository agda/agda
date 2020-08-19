{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE CPP             #-}

#if  __GLASGOW_HASKELL__ > 800
{-# OPTIONS_GHC -Wno-error=missing-signatures #-}
#endif
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

-- | Quickcheck properties for 'Agda.Utils.ListT'.

module Internal.Utils.ListT ( tests ) where

import Control.Applicative

import Data.Functor.Identity

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

prop_concat xxs = toList (concatListT (fromList (map fromList xxs))) == concat xxs

prop_idiom fs xs = toList (fromList fs <*> fromList xs) == (fs <*> xs)

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
