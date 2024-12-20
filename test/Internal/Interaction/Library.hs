{-# LANGUAGE TemplateHaskell #-}

module Internal.Interaction.Library ( tests ) where

import qualified Data.Text as T
import Test.QuickCheck

import Agda.Syntax.Common.Pretty     ( prettyShow )
import Agda.Interaction.Library.Base ( LibName(LibName) )
import Agda.Interaction.Library
import Agda.Utils.Functor

import Internal.Helpers

------------------------------------------------------------------------
-- * Instances
------------------------------------------------------------------------

-- | Version numbers must be non-negative.
instance Arbitrary LibName where
  arbitrary = LibName
    <$> (T.pack . filter (/= '-') <$> arbitrary)
    <*> (map getNonNegative <$> arbitrary)

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

-- Note: the @once@ trick is obsolete for the newest QuickCheck versions (e.g. 2.10.0.1).
prop_parseLibName_example :: Property
prop_parseLibName_example = once $ and
  [ parseLibName "foo-1.2.3"    == LibName "foo" [1, 2, 3]
  , parseLibName "foo-001.02.3" == LibName "foo" [1, 2, 3]
  , parseLibName "bar"          == LibName "bar" []
  , parseLibName "alpha.beta.eta.zeta-20938847820938572093858730945873094857304985730495837203948203"
      == LibName "alpha.beta.eta.zeta"
                                   [ 20938847820938572093858730945873094857304985730495837203948203 ]
  ]

-- | Test that printing then parsing a library name is the identity.
--
--   The other way round does not strictly hold, e.g.
--   @prettyShow (parseLibName "foo-00") = "foo-0"@.
--   Since random strings give seldom interesting version views,
--   we would need a custom generator to test it effectively.
prop_parseLibName_roundtrip :: LibName -> Bool
prop_parseLibName_roundtrip vv = vv == parseLibName (prettyShow vv)

-- | Examples for 'findLib'.
prop_findLib_example :: Property
prop_findLib_example = once $ and
  [ findLib' id (l "a"  ) (map l [ "a-1", "a-02", "a-2", "b"      ]) == (map l [ "a-02", "a-2" ])
  , findLib' id (l "a"  ) (map l [ "a", "a-1", "a-01", "a-2", "b" ]) == (map l [ "a"           ])
  , findLib' id (l "a-1") (map l [ "a", "a-1", "a-01", "a-2", "b" ]) == (map l [ "a-1", "a-01" ])
  , findLib' id (l "a-2") (map l [ "a", "a-1", "a-01", "a-2", "b" ]) == (map l [ "a-2"         ])
  , findLib' id (l "c"  ) (map l [ "a", "a-1", "a-01", "a-2", "b" ]) == (map l [               ])
  ]
  where l = parseLibName

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
tests = testProperties "Internal.Interaction.Library" $allProperties
