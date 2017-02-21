module Main (main) where

import qualified CompilerTest     as Compiler
import           Test.Tasty


main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [Compiler.unitTests]
