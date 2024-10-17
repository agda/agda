module LetRecordPattern where

open import Agda.Builtin.Nat

record Foo : Set where
  constructor mk
  field
    foo : Nat

test : Foo → Nat
test =
  let
    unfoo : Foo → Nat
    unfoo (mk x) = x
  in unfoo
