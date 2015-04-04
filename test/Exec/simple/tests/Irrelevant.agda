module tests.Irrelevant where

open import Prelude.IO
open import Prelude.Nat
open import Prelude.Unit

A : Set
A = Nat

record R : Set where
  id : A → A
  id x = x

postulate r : R

id2 : .A → A → A
id2 x y = y

open R

main : IO Unit
main = printNat (id2 10 20) ,,
  printNat (id r 30) ,,
  return unit
