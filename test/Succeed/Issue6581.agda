{-# OPTIONS --safe --cubical #-}
module Issue6581 where

open import Agda.Builtin.Cubical.Sub
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

f : ∀ {A P} → Σ A P → A
f (x , y) = x

_ : f (primTransp (λ _ → Σ Nat (λ _ → Nat)) i0 (zero , zero)) ≡ zero
_ = refl

module
  _ {A : Set} {P : A → Set} (φ : I)
    (uf : I → Partial φ A) (us : (i : I) → PartialP φ (λ .o → P (uf i o) ))
    (u0f : Sub A φ (uf i0)) (u0s : Sub (P (primSubOut u0f)) φ λ { (φ = i1) → us i0 itIsOne })
  where

  test : Σ A P
  test = primHComp {A = Σ A P} {φ = φ} (λ i .o → uf i o , us i o) (primSubOut u0f , primSubOut u0s)

  _ : f test ≡ primComp (λ _ → A) uf (primSubOut u0f)
  _ = refl
