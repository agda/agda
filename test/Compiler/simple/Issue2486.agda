module Issue2486 where

open import Common.Prelude
open import Issue2486.Import

f : MyList String → String
f [] = "sdf"
f (x :: _) = x

xs : MyList String
xs = "sdfg" :: []

main : IO Unit
main =
  putStrLn (f xs)
