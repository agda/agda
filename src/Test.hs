module Test (main) where

import Backend
import Agda.Main (runAgda)

main :: IO ()
main = runAgda [backend]
