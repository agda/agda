{-# OPTIONS --safe --cubical #-}
module Issue6581 where

open import Agda.Primitive.Cubical
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

record Σ (A : Set) (P : A → Set) : Set where
  no-eta-equality
  pattern
  constructor _,_
  field
    fst : A
    snd : P fst

open Σ public

test : Σ Nat (λ _ → Nat)
test = primTransp (λ _ → Σ Nat (λ _ → Nat)) i0 (zero , zero)

f : Σ Nat (λ _ → Nat) → Nat
f (x , y) = x

_ : f test ≡ zero
_ = refl -- f (primTransp (λ _ → Σ Nat (λ _ → Nat)) i0 (zero , zero)) != zeroodule Test9 where
