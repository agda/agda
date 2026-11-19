{-# LANGUAGE TemplateHaskell #-}

module Internal.Utils.Word
  ( tests
  )
  where

import Data.Word (Word32)

import Agda.Utils.Word (monus)

import Internal.Helpers

prop_monus_non_negative :: (Num a, Ord a) => a -> a -> Bool
prop_monus_non_negative x y = monus x y >= 0

prop_monus_Word32 :: Word32 -> Word32 -> Property
prop_monus_Word32 x y =
  toInteger (monus x y) === max 0 (toInteger x - toInteger y)

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
tests = testProperties "Internal.Utils.Word" $allProperties
