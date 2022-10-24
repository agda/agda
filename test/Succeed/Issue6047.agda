{-# OPTIONS --cubical #-}

module Issue6047 where

open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Nat
open import Agda.Primitive

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (suc n)
  suc  : {n : Nat} (i : Fin n) → Fin (suc n)

data ⊥ : Set where

toℕ : ∀ {n} → Fin n → Nat
toℕ zero    = 0
toℕ (suc i) = suc (toℕ i)

postulate
  inj-toℕ : {n : Nat} {k l : Fin n} → (toℕ k ≡ toℕ l) → k ≡ l
  isSetℕ : (x y : Nat) (p q : x ≡ y) → p ≡ q

ap : ∀ {A : Set} {B : A → Set} (f : ∀ x → B x) → ∀ {x y : A} (p : x ≡ y)
   → PathP (λ i → B (p i)) (f x) (f y)
ap f p i = f (p i)

inj-cong : {n : Nat} {k l : Fin n} → (p : toℕ k ≡ toℕ l) → ap toℕ (inj-toℕ p) ≡ p
inj-cong p = isSetℕ _ _ _ _
