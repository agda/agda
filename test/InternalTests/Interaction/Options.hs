{-# LANGUAGE CPP #-}

module InternalTests.Interaction.Options ( tests ) where

import Agda.Interaction.Options

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$>) )
#endif

import Data.List

import InternalTests.Helpers

prop_defaultOptions :: IO Bool
prop_defaultOptions =
  either (const False) (const True) <$> runOptM (checkOpts defaultOptions)

-- | The default pragma options should be considered safe.

defaultPragmaOptionsSafe :: IO Bool
defaultPragmaOptionsSafe
    | null unsafe = return True
    | otherwise   = do putStrLn $ "Following pragmas are default but not safe: "
                                        ++ intercalate ", " unsafe
                       return False
  where unsafe = unsafePragmaOptions defaultPragmaOptions

------------------------------------------------------------------------
-- All tests

tests :: IO Bool
tests = runTests "InternalTests.Interaction.Options"
  [ prop_defaultOptions
  , defaultPragmaOptionsSafe
  ]
