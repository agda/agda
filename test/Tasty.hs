module Main (main) where

import qualified CompilerTest     as Compiler
import           Test.Tasty


main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests, goldenTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [Compiler.unitTests]

goldenTests :: TestTree
goldenTests = testGroup "Golden tests"
  [Compiler.goldenTests]
