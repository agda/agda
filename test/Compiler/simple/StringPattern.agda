-- test for pattern matching on Strings
module StringPattern where

open import Common.IO
open import Common.Unit
open import Common.String

f : String → String
f "bla" = "found-bla"
f x = x

-- expected:
-- no-bla
-- found-bla
main : IO Unit
main =
  putStrLn (f "no-bla") ,,
  putStrLn (f "bla")
