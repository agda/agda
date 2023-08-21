-- | `doctest-parallel` runner for the `Agda` library.
module Main where

import System.Environment
         ( getArgs )
import Test.DocTest
         ( mainFromLibrary )
import Test.DocTest.Helpers
         ( extractSpecificCabalLibrary, findCabalPackage )

-- | Doctest @Agda:Agda@.
main :: IO ()
main = do
  args <- getArgs
  pkg  <- findCabalPackage "Agda"
  -- Need to give the library name, otherwise the parser does not find it.
  lib  <- extractSpecificCabalLibrary Nothing pkg
  mainFromLibrary lib args
