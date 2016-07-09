
module InternalTests.Syntax.Parser.Parser ( tests ) where

import Agda.Syntax.Parser.Parser

import InternalTests.Helpers

------------------------------------------------------------------------------

prop_splitOnDots :: Bool
prop_splitOnDots = and
  [ splitOnDots ""         == [""]
  , splitOnDots "foo.bar"  == ["foo", "bar"]
  , splitOnDots ".foo.bar" == ["", "foo", "bar"]
  , splitOnDots "foo.bar." == ["foo", "bar", ""]
  , splitOnDots "foo..bar" == ["foo", "", "bar"]
  ]

{--------------------------------------------------------------------------
    Tests
 --------------------------------------------------------------------------}

-- | Test suite.
tests :: IO Bool
tests = runTests "InternalTests.Parser.Parser"
  [ quickCheck' prop_splitOnDots
  ]
