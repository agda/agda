{-# LANGUAGE DoAndIfThenElse, TypeSynonymInstances, FlexibleInstances, OverloadedStrings #-}
module Main where

import qualified Exec.Tests as EXEC
import Test.Tasty
import Test.Tasty.Silver.Interactive as TM
import Control.Applicative


main :: IO ()
main = tests >>= TM.defaultMain

tests :: IO TestTree
tests = testGroup "all" <$> sequence [EXEC.tests]

