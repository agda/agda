{-# LANGUAGE CPP             #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module InternalTests.Interaction.Library ( tests ) where

import Control.Applicative ( liftA2, (<$>), (<*>) )
import Test.QuickCheck

import Agda.Interaction.Library
import Agda.Utils.Functor

-- import InternalTests.Helpers

------------------------------------------------------------------------
-- * Instances
------------------------------------------------------------------------

-- | Version numbers must be non-negative.
instance Arbitrary VersionView where
  arbitrary = liftA2 VersionView arbitrary $ map getNonNegative <$> arbitrary

------------------------------------------------------------------------
-- * Properties
------------------------------------------------------------------------

-- Note: the @once@ trick is obsolete for the newest QuickCheck versions (e.g. 2.10.0.1).
prop_versionView_example :: Property
prop_versionView_example = once $ and
  [ versionView "foo-1.2.3"    == VersionView "foo" [1, 2, 3]
  , versionView "foo-001.02.3" == VersionView "foo" [1, 2, 3]
  , versionView "bar"          == VersionView "bar" []
  , versionView "alpha.beta.eta.zeta-20938847820938572093858730945873094857304985730495837203948203"
      == VersionView "alpha.beta.eta.zeta"
                                   [ 20938847820938572093858730945873094857304985730495837203948203 ]
  ]

-- | Test that printing then parsing a version view is the identity.
--
--   The other way round does not strictly hold, e.g.
--   @unVersionView (versionView "foo-00") = "foo-0"@.
--   Since random strings give seldom interesting version views,
--   we would need a custom generator to test it effectively.
prop_versionView_roundtrip :: VersionView -> Bool
prop_versionView_roundtrip vv = vv == versionView (unVersionView vv)

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $quickCheckAll work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'quickCheckAll'.
--
--   Using 'quickCheckAll' is convenient and superior to the manual
--   enumeration of tests, since the name of the property is
--   added automatically.

tests :: IO Bool
tests = do
  putStrLn "InternalTests.Interaction.Library"
  $quickCheckAll
