{-# OPTIONS --rewriting --local-confluence-check #-}

open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

variable
  A : Set
  n m l : Nat

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : A → Vec A n → Vec A (suc n)

variable
  xs ys zs : Vec _ _

_++_ : Vec A n → Vec A m → Vec A (n + m)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

postulate
  +-assoc : (n + m) + l ≡ n + (m + l)

{-# REWRITE +-assoc #-}

postulate
  ++-assoc : _++_ {n = ⟨ _ ⟩} (xs ++ ys) zs ≡ xs ++ (ys ++ zs)

{-# REWRITE ++-assoc #-}

test₁ : ∀ {xs : Vec A zero} → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
test₁ = refl

test₂ : ∀ {xs : Vec A (suc n)} → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
test₂ = refl
