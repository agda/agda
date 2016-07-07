{-# LANGUAGE TemplateHaskell #-}

module InternalTests.TypeChecking.Positivity ( tests ) where

import Agda.TypeChecking.Positivity

import Agda.Utils.SemiRing

import Test.QuickCheck

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
