{-# LANGUAGE TemplateHaskell #-}

module Internal.Interaction.Options ( tests ) where

import Agda.Interaction.Options

import Data.List

import Internal.Helpers

prop_defaultOptions :: Property
prop_defaultOptions = ioProperty $
  either (const False) (const True) <$> runOptM (checkOpts defaultOptions)

-- | The default pragma options should be considered safe.

prop_defaultPragmaOptionsSafe :: Property
prop_defaultPragmaOptionsSafe = ioProperty helper
  where
    helper :: IO Bool
    helper
      | null unsafe = return True
      | otherwise   = do putStrLn $ "Following pragmas are default but not safe: "
                                          ++ intercalate ", " unsafe
                         return False
        where unsafe = unsafePragmaOptions defaultPragmaOptions

------------------------------------------------------------------------
-- * All tests
------------------------------------------------------------------------

-- Template Haskell hack to make the following $allProperties work
-- under ghc-7.8.
return [] -- KEEP!

-- | All tests as collected by 'allProperties'.
-- Using 'allProperties' is convenient and superior to the manual
-- enumeration of tests, since the name of the property is added
-- automatically.

tests :: TestTree
tests = quickCheck2Tasty "Internal.Interaction.Options" $allProperties
