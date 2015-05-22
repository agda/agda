module Irrelevant where

open import Common.IO
open import Common.Nat
open import Common.Unit

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
