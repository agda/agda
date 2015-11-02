module Main where

import MAlonzo.Code.ExportTestAgda
import Data.Text

main :: IO ()
main = putStrLn $ Data.Text.unpack itWorksText
