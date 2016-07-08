{-# LANGUAGE CPP #-}

module InternalTests.TypeChecking.SizedTypes.WarshallSolver () where

import Agda.TypeChecking.SizedTypes.Syntax
import Agda.TypeChecking.SizedTypes.WarshallSolver

#if __GLASGOW_HASKELL__ <= 708
import Control.Applicative ( (<$>), (<*>) )
#endif

import InternalTests.TypeChecking.SizedTypes.Syntax ()

import Test.QuickCheck

------------------------------------------------------------------------------
-- QuickCheck instances

instance Arbitrary Weight where
  arbitrary = frequency
    [ (1, return Infinity)
    , (5, Offset . O <$> choose (0, 200))
    ]

instance Arbitrary Label where
  arbitrary = frequency
    [ (1, return LInf)
    , (5, Label <$> arbitrary <*> arbitrary)
    ]

