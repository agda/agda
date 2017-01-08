{-# LANGUAGE CPP #-}

module InternalTests.Syntax.Concrete.Name () where

import Agda.Syntax.Concrete.Name

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$>), (<*>) )
#endif

import Data.List

import InternalTests.Syntax.Common ()
import InternalTests.Syntax.Position ()

import Test.QuickCheck

------------------------------------------------------------------------
-- * QuickCheck instances
------------------------------------------------------------------------

instance Arbitrary TopLevelModuleName where
  arbitrary = TopLevelModuleName <$> arbitrary <*> listOf1 (listOf1 $ elements "AB")

instance CoArbitrary TopLevelModuleName where
  coarbitrary (TopLevelModuleName _ m) = coarbitrary m

instance Arbitrary Name where
  arbitrary = oneof
    [ Name   <$> arbitrary <*> parts
    , NoName <$> arbitrary <*> arbitrary
    ]
    where
    parts = do
      parts         <- listOf1 (elements ["x", "y", "z"])
      startWithHole <- arbitrary
      endWithHole   <- arbitrary
      return $
        (if startWithHole then (Hole :)    else id) $
        (if endWithHole   then (++ [Hole]) else id) $
        intersperse Hole (map Id parts)

instance CoArbitrary NamePart

instance CoArbitrary Name where
  coarbitrary (Name _ ns)  = variant 0 . coarbitrary ns
  coarbitrary (NoName _ i) = variant 1 . coarbitrary i
