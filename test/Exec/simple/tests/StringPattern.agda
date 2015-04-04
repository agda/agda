-- test for pattern matching on Strings
module tests.StringPattern where

open import Prelude.IO
open import Prelude.Unit
open import Prelude.String

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
