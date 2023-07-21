module OpaqueUnfoldLiftType where

open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat hiding (_+_)

record ⊤* ℓ : Set ℓ where

level-of : ∀ {ℓ} → Set ℓ → _
level-of {ℓ = ℓ} _ = ℓ

opaque
  Vec : ∀ {ℓ} → Set ℓ → Nat → Set ℓ
  Vec A zero    = ⊤* _
  Vec A (suc n) = Σ A λ _ → Vec A n

opaque
  unfolding Vec

  nil : ∀ {ℓ} {A : Set ℓ} → Vec A zero
  nil = record{}

variable
  A : Set
  n k : Nat

opaque
  _+_ : Nat → Nat → Nat
  zero + x = x
  suc n + x = suc (n + x)

opaque
  unfolding _+_

  +-zero-l : ∀ x → zero + x ≡ x
  +-zero-l x = refl

opaque
  unfolding _+_ Vec

  _⊕_ : Vec A n → Vec A k → Vec A (n + k)
  _⊕_ {n = zero} xs ys = ys
  _⊕_ {n = suc n} (x , xs) ys = x , xs ⊕ ys

opaque
  unfolding _⊕_

  private
    ⊕-zero-l-type : ∀ (x : Vec A n) → Set (level-of A)
    ⊕-zero-l-type {A = A} x = nil {A = A} ⊕ x ≡ x

  ⊕-zero-l : ∀ (x : Vec A n) → ⊕-zero-l-type x
  ⊕-zero-l x = refl
