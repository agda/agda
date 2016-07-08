{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}

module InternalTests.TypeChecking.Positivity ( tests ) where

import Agda.TypeChecking.Positivity

import Agda.Utils.SemiRing

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$>), (<*>) )
#endif

import InternalTests.Syntax.Abstract.Name ()
import InternalTests.TypeChecking.Positivity.Occurrence ()

import Test.QuickCheck

------------------------------------------------------------------------
-- * Generators and tests
------------------------------------------------------------------------

instance Arbitrary OccursWhere where
  arbitrary = oneof [return Unknown, Known <$> arbitrary]

  shrink Unknown    = []
  shrink (Known ws) = Unknown : [ Known ws | ws <- shrink ws ]

instance Arbitrary Where where
  arbitrary = oneof
    [ return LeftOfArrow
    , DefArg <$> arbitrary <*> arbitrary
    , return UnderInf
    , return VarArg
    , return MetaArg
    , ConArgType <$> arbitrary
    , IndArgType <$> arbitrary
    , InClause <$> arbitrary
    , return Matched
    , InDefOf <$> arbitrary
    ]

instance CoArbitrary OccursWhere where
  coarbitrary (Known ws) = variant 0 . coarbitrary ws
  coarbitrary Unknown    = variant 1

instance CoArbitrary Where where
  coarbitrary LeftOfArrow    = variant 0
  coarbitrary (DefArg a b)   = variant 1 . coarbitrary (a, b)
  coarbitrary UnderInf       = variant 2
  coarbitrary VarArg         = variant 3
  coarbitrary MetaArg        = variant 4
  coarbitrary (ConArgType a) = variant 5 . coarbitrary a
  coarbitrary (IndArgType a) = variant 6 . coarbitrary a
  coarbitrary (InClause a)   = variant 7 . coarbitrary a
  coarbitrary Matched        = variant 8
  coarbitrary (InDefOf a)    = variant 9 . coarbitrary a

instance Arbitrary Edge where
  arbitrary = Edge <$> arbitrary <*> arbitrary

  shrink (Edge o w) = [ Edge o w | o <- shrink o ] ++
                      [ Edge o w | w <- shrink w ]

instance CoArbitrary Edge where
  coarbitrary (Edge o w) = coarbitrary (o, w)

------------------------------------------------------------------------------

-- | The 'oplus' method for 'Occurrence' matches that for 'Edge'.

prop_oplus_Occurrence_Edge :: Edge -> Edge -> Bool
prop_oplus_Occurrence_Edge e1@(Edge o1 _) e2@(Edge o2 _) =
  case oplus e1 e2 of
    Edge o _ -> o == oplus o1 o2

-- Template Haskell hack to make the following $quickCheckAll work
-- under GHC 7.8.
return []

-- | Tests.

tests :: IO Bool
tests = do
  putStrLn "InternalTests.TypeChecking.Positivity"
  $quickCheckAll
