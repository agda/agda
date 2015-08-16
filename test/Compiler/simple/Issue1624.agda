module Issue1624 where

open import Common.Char
open import Common.String
open import Common.List

test : List Char → String
test ('0' ∷ ('x' ∷ xs)) = "x"
test ('0' ∷ ('b' ∷ xs)) = "b"
test xs               = "f"


open import Common.IO
open import Common.Unit

main : IO Unit
main = putStr (test x)
  where x = '0' ∷ ('x' ∷ ('1' ∷ []))
