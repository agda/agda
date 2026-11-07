module Issue434 where

open import Common.IO
open import Common.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

record R : Set₁ where
  constructor mk
  field A : Set

  F : Bool → Set
  F true = A
  F false = A → A

  iterate : Nat → (A → A) → A → A
  iterate zero f a = a
  iterate (suc n) f a = iterate n f (f a)

  field value : (b : Bool) → F b

  run : Nat → A
  run n = iterate n (value false) (value true)

r : R
r = mk Nat (λ { true → zero ; false → suc })

main : IO Unit
main = printNat (R.run r 4)
