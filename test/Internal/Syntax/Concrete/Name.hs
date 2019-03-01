
module Internal.Syntax.Concrete.Name () where

import Agda.Syntax.Concrete.Name

import Data.List

import Internal.Syntax.Common ()
import Internal.Syntax.Position ()

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
    [ Name   <$> arbitrary <*> pure InScope <*> parts
    , NoName <$> arbitrary <*> arbitrary
    , RecordName <$> arbitrary <*> arbitrary
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
  coarbitrary (Name _ _ ns) = variant 0 . coarbitrary ns
  coarbitrary (NoName _ i)  = variant 1 . coarbitrary i
  coarbitrary (RecordName _ i)  = variant 2 . coarbitrary i
