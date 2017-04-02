module Main where

import System.Process
import System.Directory

main :: IO ()
main = withCurrentDirectory "benchmark/agda2mlf" $
  callProcess "./run.sh" []
