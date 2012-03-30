{-# LANGUAGE CPP #-}

------------------------------------------------------------------------
-- | Utilities for the 'Either' type
------------------------------------------------------------------------

module Agda.Utils.Either
  ( mapEither, mapLeft, mapRight
  , isLeft, isRight
  , allRight
  , tests
  ) where

import Control.Arrow
import Agda.Utils.QuickCheck
import Agda.Utils.TestHelpers

#include "../undefined.h"
import Agda.Utils.Impossible

-- | 'Either' is a bifunctor.

mapEither :: (a -> c) -> (b -> d) -> Either a b -> Either c d
mapEither f g = either (Left . f) (Right . g)

-- | 'Either _ b' is a functor.

mapLeft :: (a -> c) -> Either a b -> Either c b
mapLeft f = mapEither f id

-- | 'Either a' is a functor.

mapRight :: (b -> d) -> Either a b -> Either a d
mapRight = mapEither id

-- | Returns 'True' iff the argument is @'Right' x@ for some @x@.

isRight :: Either a b -> Bool
isRight (Right _) = True
isRight (Left  _) = False

-- | Returns 'True' iff the argument is @'Left' x@ for some @x@.

isLeft :: Either a b -> Bool
isLeft (Right _) = False
isLeft (Left _)  = True

-- | Returns @'Right' <input with tags stripped>@ if all elements are
-- to the right, and otherwise @Left <input>@:
--
-- @
--  allRight xs ==
--    if all isRight xs then
--      Right (map (\(Right x) -> x) xs)
--     else
--      Left xs
-- @

allRight :: [Either a b] -> Either [Either a b] [b]
allRight []              = Right []
allRight xs@(Left _ : _) = Left xs
allRight (Right b : xs)  = case allRight xs of
  Left  xs -> Left (Right b : xs)
  Right bs -> Right (b : bs)

prop_allRight xs =
  allRight xs ==
    if all isRight xs then
      Right (map fromRight xs)
     else
      Left xs
  where
  fromRight (Right x) = x
  fromRight (Left _)  = __IMPOSSIBLE__

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "Agda.Utils.Either"
  [ quickCheck' (prop_allRight :: [Either Integer Bool] -> Bool)
  ]
