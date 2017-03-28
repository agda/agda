module Main (main) where

import qualified CompilerTest     as Compiler
import           Test.Tasty
import           System.Directory (withCurrentDirectory)

-- Note that we need to change directory because of where the golden test-files are located
main :: IO ()
main = withCurrentDirectory "test/agda2mlf" $ defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [unitTests, goldenTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests"
  [Compiler.unitTests]

goldenTests :: TestTree
goldenTests = testGroup "Golden tests"
  [Compiler.goldenTests]
